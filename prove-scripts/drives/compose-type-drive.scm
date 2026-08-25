;;; compose-type-drive.scm -- LANDED 2026-08-23.  Kept as the record of the
;;; obstacle and of the migration; the proof itself now lives in
;;; theorem-library/compose-apply-proof.scm, installed under the name
;;; `compose-type' (not `compose-type-guarded'), and the six citation sites
;;; below were migrated the same day -- one line each, and NOT the line the
;;; table predicted at product-weights.scm, where A is NN, not PTS(P1).
;;; The support in structure-library/compose.scm is retired.
;;;
;;; What follows is the hand-off note as it stood before the user's call.
;;;
;;; `compose-apply' is now PROVEN modulo 0 (theorem-library/compose-apply-proof.scm).
;;; Its sibling `compose-type' (structure-library/compose.scm:41) is the LAST
;;; leaf of fourteen bills -- compose-continuous-at, deriv-chain, deriv-chain-value,
;;; deriv-inverse, continuous-at-implies-sequential, continuous-at-iff-sequential,
;;; product-identity-continuous, product-weights-equivalent, dir-diff-reparam,
;;; dir-diff-scale, dir-diff-shift, dir-deriv-homogeneous, dir-deriv-mvt,
;;; dir-deriv-linear -- and it is NOT a driver problem.  It is a STATEMENT problem,
;;; and the decision is the user's.
;;;
;;; THE OBSTACLE, stated exactly.  compose-type is
;;;
;;;     g in FUN(A,B) and f in FUN(B,C)  =>  COMPOSE(f,g) in FUN(A,C)
;;;
;;; Unfolding COMPOSE gives the lambda VNB-LAMBDA z_ in DOM(g). f(g(z_)), so
;;; `lam-t' can only conclude membership in FUN(DOM(g), C).  Getting from there
;;; to FUN(A, C) is `dom-of-fun' (theory.scm:500)
;;;
;;;     f in FUN(A) and A in SET  =>  DOM(f) in SET and DOM(f) = A
;;;
;;; whose second hypothesis, (IN A SET), NOTHING IN THE TREE DERIVES from
;;; (IN g (FUN A B)).  That was checked, not assumed:
;;;
;;;   * `fun-set-iff' (theory.scm:412) is about FUN(A,B) BEING a set, not about
;;;     its having a member.
;;;   * `is-fun-def' (:479) existentially quantifies a SET domain, so it delivers
;;;     sethood of SOME witness, not of the A one already holds.
;;;   * `(IN (DOM f) SET)' occurs in exactly ONE place in the whole tree --
;;;     inside dom-of-fun itself, guarded on (IN A SET).  There is no
;;;     "a set-valued function has a set domain".
;;;   * `lam-t' independently OPENS an (IN (DOM g) SET) leaf, so the sethood is
;;;     owed twice over.
;;;
;;; Mathematically the missing fact is true and is REPLACEMENT: g is a set
;;; (membership-implies-sethood), DOM(g) is the image of g under the
;;; first-projection, hence a set (`image-set', structure-library/injection.scm,
;;; primitive), A has the same members as DOM(g) (`dom-fun-membership'), and a
;;; subclass of a set is a set (`subset-of-set-is-set',
;;; theorem-library/subset-lemmas.scm:85).  The step that is NOT available is the
;;; middle one: naming the first-projection as a class function that IMAGE can
;;; take.  Building that is set-theory machinery, and it is the expensive road.
;;;
;;; THE CHEAP ROAD, and it WORKS -- the body of this file is the whole proof,
;;; run and closed `modulo 0' on 2026-08-23.  GUARD compose-type on (IN A SET).
;;; Everything else in the derivation is already in the tree.
;;;
;;; WHAT THE GUARD COSTS: six `fact' sites, all of them in loaded proof files,
;;; and at every one of them A is a class whose sethood is one line away --
;;;
;;;   theorem-library/chain-rule.scm:243, :246          A = RR    -> rr-is-set  (primitive)
;;;   theorem-library/inverse-function.scm:256          A = RR    -> rr-is-set
;;;   theorem-library/sequential-continuity.scm:188     A = NN    -> nn-is-set  (primitive)
;;;   theorem-library/product-weights.scm:221           A = PTS(P1) -- the file
;;;       ALREADY lands (IN pw-c1 SET) at :175, off the IS-METRIC-SPACE typing conjunct
;;;   theorem-library/continuity-compose.scm:219        A = PTS(RR-MS) -> rr-ms-carrier + rr-is-set
;;;
;;; (calculus/probe-314-mach.scm:37 cites it too but is not in load.scm.)
;;; `compose-type-2..5' in structure-library/compose-typing.scm are SEPARATE
;;; statements over RAN and do not cite compose-type; they are untouched.
;;;
;;; SO THE QUESTION FOR THE USER is which of the two the statement should be:
;;; the unguarded one, honest only if the replacement route is built, or the
;;; guarded one, provable today at the price of six one-line citations.  The
;;; standing preference in this tree is "state the hypothesis, pay the
;;; migration"; that call was not made here because migrating six live proofs
;;; is a separate measurement.
;;;
;;; Run:   ./prover -i prove-scripts/drives/compose-type-drive.scm

(define (ct-asm what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ct-asm: no assumption is" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; compose-type, GUARDED on (IN A SET).  Closes; bill is modulo 0.
(sp (make-wff
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (IN A SET)
       (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
         (IN (COMPOSE f g) (FUN A C)))))))))))
(dk-peel-to! 'IN)
(ai '(AND (IN g (FUN a b)) (IN f (FUN b c))))

;; (IN g (FUN a)) off fun-codomain-iff.  In a have! LANE: mac-h is destructive
;; and the main branch still needs (IN g (FUN a b)) intact.
(have! '(IN g (FUN a))
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff '(IN g (FUN a b))))))
    (ass)))

;; dom-of-fun has an AND antecedent, so `fact' will not detach it: assemble the
;; conjunction first (the CLAUDE.md rule for ord-le-total and friends).
(have! '(AND (IN g (FUN a)) (IN a SET)))
(dk-split! (dk-fact! 'dom-of-fun 'a 'g))        ; lands (= (DOM g) a) and (IN (DOM g) SET)

(mac 'COMPOSE)                                  ; (IN (VNB-LAMBDA z_ (DOM g) (f (g z_))) (FUN a c))
(subst '(= (DOM g) a))                          ; ... (VNB-LAMBDA z_ a ...) -- a BINDER domain,
                                                ; which subst does reach; the head is not in
                                                ; operator position here.
(dk-lam-t!)                                     ; closes the (IN a SET) leaf, leaves the typing one
(di)
(let* ((gz (cadr (cadr (dk-goal))))             ; (g z)
       (z  (cadr gz)))
  (fact 'fun-apply-type-c 'g 'a 'b z)           ; (IN (g z) b)
  (fact 'fun-apply-type-c 'f 'b 'c gz)          ; (IN (f (g z)) c)
  (ass))
(qed 'compose-type-guarded)
