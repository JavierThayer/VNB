;;; ord-well-ordered-proof.scm -- the well-ordering of ORD, PROVEN.
;;;
;;;   cl subset ORD,  cl nonempty  =>  cl has a <=_ORD-least element
;;;
;;; This was a `support' in structure-library/ordinals.scm carrying a warrant of
;;; kind `proof' that named no file -- one of the 44 the load's
;;; proof-warrant-audit reports, where the warrant recites a derivation instead
;;; of pointing at a machine proof.  The derivation its comment gave is correct,
;;; and this is it, mechanised.  The warrant is now the file.
;;;
;;; THE ARGUMENT.  Proof by contradiction: assume cl has no <=_ORD-least
;;; element.  Then show by transfinite induction that NO ordinal is in cl --
;;; because if a were in cl and every ordinal below a were outside cl, then a
;;; would BE least, contradicting the assumption.  Since cl is nonempty and
;;; contained in ORD, that is absurd.
;;;
;;; The informal argument is usually stated with the class C = { a : a not in
;;; cl }.  It stays implicit here: the `tfi' rule takes
;;;   (FORALL v (IMPLIES (IN v ORD) P))
;;; straight to the strong-induction form
;;;   (FORALL v (IMPLIES (AND (IN v ORD) (FORALL b (IMPLIES (<_ORD b v) P[b]))) P))
;;; so P = (NOT (IN v cl)) is all that is needed and no comprehension is formed.
;;;
;;; Rests on NOTHING but the primitive ordinal shelf: transfinite-induction (via
;;; tfi), ord-le-total, ord-le-refl, ord-lt-iff.  No library theorem is cited,
;;; which is why it can load this early -- and it must, since nn-least-element
;;; and every use of minimize! sit downstream of it.
;;;
;;; The one non-obvious mechanical step is the k <= a branch: ord-lt-iff is an
;;; IFF, so `ai' lands BOTH directions and the wanted one has to be detached
;;; explicitly before the induction hypothesis will fire at k.

(define OWO-LEAST
  '(FORSOME m (AND (IN m cl) (FORALL k (IMPLIES (IN k cl) (<=_ORD m k))))))
(define OWO-SUB '(FORALL x (IMPLIES (IN x cl) (IN x ORD))))
(define OWO-NE  '(FORSOME w (IN w cl)))
(define OWO-NONE '(FORALL a (IMPLIES (IN a ORD) (NOT (IN a cl)))))

(sp (make-wff (list 'FORALL 'cl (list 'IMPLIES (list 'AND OWO-SUB OWO-NE) OWO-LEAST))))
(di) (di)
(dk-split! (list 'AND OWO-SUB OWO-NE))

(pbc)

;;; ---- the induction: no ordinal is in cl ----
(have! OWO-NONE
  (lambda ()
    (tfi)
    (di)                                        ; introduces the ordinal variable only
    (let* ((ant (cadr (dk-goal)))               ; (AND (IN a ORD) IH)
           (av  (cadr (cadr ant)))              ; the eigenvariable a
           (ihf (caddr ant)))                   ; the induction hypothesis
      (di)                                      ; assume the AND
      (dk-split! ant)                           ; -> (IN a ORD), IH
      (di)                                      ; assume (IN a cl); goal FALSITY
      ;; a is least
      (have! (list 'FORALL 'k (list 'IMPLIES '(IN k cl) (list '<=_ORD av 'k)))
        (lambda ()
          (di)                                  ; k, (IN k cl)
          (inst+ OWO-SUB 'k)                    ; (IN k ORD)
          (have! (list 'AND (list 'IN av 'ORD) '(IN k ORD)))
          (fact 'ord-le-total av 'k)            ; (OR (<= a k) (<= k a))
          (use-cases
            (list (list '<=_ORD av 'k) (list '<=_ORD 'k av))
            (lambda () (ass))
            (lambda ()                          ; k <= a : rule out k < a
              (pbc)                             ; assume NOT (<= a k); goal FALSITY
              (have! (list 'NOT (list '= 'k av))
                (lambda ()
                  (di)                          ; assume (= k a); goal FALSITY
                  ;; k = a makes a <= k the reflexivity instance, which the pbc
                  ;; hypothesis denies.  `subst' reaches the GOAL, so claim the
                  ;; membership and rewrite THAT, rather than the assumption.
                  (have! (list '<=_ORD av 'k)
                    (lambda ()
                      (subst (list '= 'k av))   ; goal becomes (<=_ORD a a)
                      (fact 'ord-le-refl av)
                      (ass)))
                  (ai (list 'NOT (list '<=_ORD av 'k)))))
              (have! (list 'AND (list '<=_ORD 'k av) (list 'NOT (list '= 'k av))))
              (fact 'ord-lt-iff 'k av)          ; the IFF
              (ai (list 'IFF (list '<_ORD 'k av)
                        (list 'AND (list '<=_ORD 'k av) (list 'NOT (list '= 'k av)))))
              ;; the iff lands BOTH directions; detach the one we want
              (detach! (list 'IMPLIES
                             (list 'AND (list '<=_ORD 'k av) (list 'NOT (list '= 'k av)))
                             (list '<_ORD 'k av)))
              (inst+ ihf 'k)                    ; (NOT (IN k cl))
              (ai (list 'NOT '(IN k cl)))))))
      ;; ... so cl HAS a least element, contradicting the pbc hypothesis
      (have! OWO-LEAST
        (lambda ()
          (ew av)
          ;; the witness goal is an AND -- `di' SPLITS it, so close both leaves
          (for-each (lambda (nd) (dk-focus! nd) (ass))
                    (dk-opened (lambda () (di))))))
      (ai (list 'NOT OWO-LEAST)))))

;;; ---- and cl is nonempty, so something IS in cl ----
(define WV (cadr (dk-landed-1 (lambda () (ai OWO-NE)))))
(inst+ OWO-SUB WV)
(inst+ OWO-NONE WV)
(ai (list 'NOT (list 'IN WV 'cl)))
(qed 'ord-well-ordered)
(category! 'ord-well-ordered 'combinatorial)
