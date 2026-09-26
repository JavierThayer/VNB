;;; image-subset-codomain.scm -- the image of phi : dm -> cod lies in cod.
;;;
;;; PROVEN 2026-09-22.  The fact stood in structure-library/injection.scm as a
;;; bare `theory-add-axiom!' with no warrant (DEBT-BUNDLE s.4); no proof cited
;;; it, and batch 18-B met it on a first bill (`modulo {image-subset-codomain}
;;; [trust: none]') and routed around it.  The proof is the read-off of the image
;;; membership (`image-membership-iff', definitional) and one `fun-apply-type-c'
;;; at the witness.  The statement is copied LITERALLY from the axiom's site.

(sp (make-wff
  '(FORALL dm (FORALL cod (FORALL phi
      (IMPLIES (IN phi (FUN dm cod))
               (FORALL w
                 (IMPLIES (IN w (IMAGE phi dm)) (IN w cod)))))))))
(dk-peel!)
(mac-h 'image-membership-iff '(IN w (IMAGE phi dm)))
(let ((isc-x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
  (fact 'fun-apply-type-c 'phi 'dm 'cod isc-x)
  (subst (list '= 'w (list 'phi isc-x)))
  (ass))
(qed 'image-subset-codomain)
(topic! 'image-subset-codomain 'plumbing)
