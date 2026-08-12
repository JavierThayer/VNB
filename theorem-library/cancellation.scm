;;; cancellation.scm -- cancellation, proved ONCE where it lives, then carried.
;;;
;;; "a + c = b + c => a = b" on the naturals is not a fact about the naturals.
;;; It is a fact about GROUPS -- multiply by the inverse of c -- and NN gets it
;;; because NN is inside ZZ, whose additive structure IS a group and whose
;;; addition IS the surface `+' (ZZ-RING = [ZZ, binplus, ...], binplus(x,y) = x+y).
;;; It was previously re-proved on NN by induction, from Peano axioms it never
;;; needed.  This file is the antidote, and the worked example of the transport
;;; chain:
;;;
;;;   group-cancel-left        proved in GROUP, from the group axioms
;;;     -> ag-cancel-right     ABELIAN-GROUP (commutativity flips the side)
;;;     -> [view]              RING-ADDITIVE-AG carries it to every RING
;;;     -> [transport!]        ZZ-RING / QQ-RING, IN THE SURFACE LANGUAGE
;;;     -> nn-add-cancel       restrict to NN (NN <= ZZ).  No induction.
;;;
;;; Each arrow is a mechanism that already existed, or (the last two) one that
;;; now does.  Nothing here is asserted.

(define (cn-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cn-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (cn-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** cancellation: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w))) (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 8 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "cancellation: unfinished" name))))

;;; =======================================================================
;;; group-inv-in : the inverse of a carrier element is a carrier element.
;;;
;;; group.scm asserts only assoc / left-id / left-inv / identity-in -- there is
;;; no closure fact for groups at all.  This one is not an axiom: IS-GROUP
;;; carries the slot TYPING (INV s) : CARR(s) -> CARR(s), so unfolding IS-GROUP
;;; and applying fun-apply-type-c proves it.  INV is unary, which is why this
;;; costs one line and the binary closure (OPR) would cost the apply-tupling
;;; drill -- and the cancellation proof below is arranged to need only this one.
(sp (make-wff '(FORALL s (IMPLIES (IS-GROUP s)
                 (FORALL a (IMPLIES (IN a (CARR s))
                   (IN ((INV s) a) (CARR s))))))))
(di)(di)(di)(di)
(mac-h 'IS-GROUP '(IS-GROUP s))
(let loop ()                             ; split the unfolded conjunction
  (let ((c (find-first (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (cn-asms))))
    (when c (ai c) (loop))))
(fact 'fun-apply-type-c '(INV s) '(CARR s) '(CARR s) 'a)
(ass)
(cn-qed! 'group-inv-in)

;;; =======================================================================
;;; group-cancel-left :  c*a = c*b  =>  a = b   in any group.
;;;
;;;   a = e*a = (c'*c)*a = c'*(c*a) = c'*(c*b) = (c'*c)*b = e*b = b
;;;
;;; Only the LEFT axioms are used (left-id, left-inv), and the only typing
;;; needed is c' in CARR -- group-inv-in, above.
(sp (make-wff '(FORALL s (IMPLIES (IS-GROUP s)
                 (FORALL a (IMPLIES (IN a (CARR s))
                   (FORALL b (IMPLIES (IN b (CARR s))
                     (FORALL c (IMPLIES (IN c (CARR s))
                       (IMPLIES (= ((OPR s) c a) ((OPR s) c b))
                                (= a b))))))))))))
(di)(di)(di)(di)(di)(di)(di)(di)
(fact 'group-inv-in 's 'c)               ; (INV s)(c) in CARR(s)
(fact 'group-left-inv 's 'c)             ; (INV s)(c) * c = IDEN s
(fact 'group-left-id 's 'a)              ; IDEN s * a = a
(fact 'group-left-id 's 'b)
(fact 'group-assoc 's '((INV s) c) 'c 'a)  ; (c'*c)*a = c'*(c*a)
(fact 'group-assoc 's '((INV s) c) 'c 'b)
;; a = c'*(c*a):  rewrite the goal a = b leftwards through the chain.
(subst '(= a ((OPR s) (IDEN s) a)))                      ; a -> e*a
(subst '(= (IDEN s) ((OPR s) ((INV s) c) c)))            ; e -> c'*c
(subst '(= ((OPR s) ((OPR s) ((INV s) c) c) a)
           ((OPR s) ((INV s) c) ((OPR s) c a))))         ; assoc, left side
(subst '(= ((OPR s) c a) ((OPR s) c b)))                 ; THE hypothesis
(subst '(= ((OPR s) ((INV s) c) ((OPR s) c b))
           ((OPR s) ((OPR s) ((INV s) c) c) b)))         ; assoc back, right side
(subst '(= ((OPR s) ((INV s) c) c) (IDEN s)))            ; c'*c -> e
(subst '(= ((OPR s) (IDEN s) b) b))                      ; e*b -> b
(rfl)
(cn-qed! 'group-cancel-left)

;;; =======================================================================
;;; ag-cancel-right :  a*c = b*c => a = b  in an ABELIAN group.
;;;
;;; The side flips by commutativity (abelian-group-opr-comm, PROVEN in
;;; subtype-laws.scm), and the group fact applies because every abelian group is
;;; a group (abelian-group-is-group, likewise proven).  Stated for ABELIAN-GROUP
;;; because that -- not GROUP -- is what the RING-ADDITIVE-AG view targets.
(sp (make-wff '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
                 (FORALL a (IMPLIES (IN a (CARR s))
                   (FORALL b (IMPLIES (IN b (CARR s))
                     (FORALL c (IMPLIES (IN c (CARR s))
                       (IMPLIES (= ((OPR s) a c) ((OPR s) b c))
                                (= a b))))))))))))
(di)(di)(di)(di)(di)(di)(di)(di)
(fact 'abelian-group-is-group 's)
(fact 'abelian-group-opr-comm 's 'a 'c)   ; a*c = c*a
(fact 'abelian-group-opr-comm 's 'b 'c)   ; b*c = c*b
;; turn the hypothesis a*c = b*c into c*a = c*b, then cancel on the left.
(cut '(= ((OPR s) c a) ((OPR s) c b)))
(subst '(= ((OPR s) c a) ((OPR s) a c)))
(subst '(= ((OPR s) c b) ((OPR s) b c)))
(ass)
(fact 'group-cancel-left 's 'a 'b 'c)
(ass)
(cn-qed! 'ag-cancel-right)

;;; =======================================================================
;;; abelian-group-idempotent-is-id :  a*a = a  =>  a = e.
;;;
;;; Was asserted in abelian-group.scm and never warranted -- with 14 dependent
;;; proofs, the most-cited unjustified fact left in the library.  It is not deep:
;;; a*a = a and a*e = a give a*a = a*e, and cancelling a on the left leaves a = e.
;;; What it needs beyond group-cancel-left is the RIGHT identity, which is not a
;;; group axiom here (group.scm states only left-id) but in an ABELIAN group is
;;; one commutation away -- and IDEN(s) is in the carrier by group-identity-in.
;;; Both of those are now theorems (subtype-laws.scm), so this closes modulo 0.
;;;
;;; The prefix is peeled by a loop, not by a counted run of `di': how many `di'
;;; a shape takes is not a fact anyone should have to know (CLAUDE.md), and no
;;; intermediate goal here has `=' at its head, so the test is unambiguous.
(sp (make-wff '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
                 (FORALL a (IMPLIES (IN a (CARR s))
                   (IMPLIES (= ((OPR s) a a) a)
                            (= a (IDEN s)))))))))
(let peel ((fuel 12))
  (when (and (> fuel 0)
             (not (and (pair? (cn-goal)) (eq? (car (cn-goal)) '=))))
    (di)
    (peel (- fuel 1))))
(fact 'abelian-group-is-group 's)
(fact 'group-identity-in 's)                            ; e in CARR(s)
(fact 'abelian-group-opr-comm 's 'a '(IDEN s))          ; a*e = e*a
(fact 'group-left-id 's 'a)                             ; e*a = a
;; a*a = a*e, by rewriting each side down to a.
(cut '(= ((OPR s) a a) ((OPR s) a (IDEN s))))
(subst '(= ((OPR s) a a) a))                            ; the hypothesis
(subst '(= ((OPR s) a (IDEN s)) ((OPR s) (IDEN s) a)))  ; commute
(subst '(= ((OPR s) (IDEN s) a) a))                     ; left identity
(rfl)
;; cancel a on the left:  a*a = a*e  =>  a = e.
(fact 'group-cancel-left 's 'a '(IDEN s) 'a)
(ass)
(cn-qed! 'abelian-group-idempotent-is-id)

;;; =======================================================================
;;; Carry it to the rings, and then to the numbers.
;;;
;;; view-as-auto-specialize! runs inside def-functor, i.e. when views.scm loads
;;; -- long before any proof exists.  A law proved HERE is therefore invisible
;;; to it, so we re-run it: it walks the theorem table again and specializes
;;; every IS-ABELIAN-GROUP-generic theorem through the view.  That is what
;;; delivers the RING form of ag-cancel-right,
;;;
;;;     forall r. IS-RING(r) => forall a,b,c in CARR(r).
;;;                 (ADD r)(a,c) = (ADD r)(b,c) => a = b
;;;
;;; under the name ag-cancel-right-ring-additive-ag.
(view-as-auto-specialize! 'RING-ADDITIVE-AG)

;;; The module view needs the same treatment, for a sharper reason and in a
;;; narrower form.  abelian-group-idempotent-is-id used to be an AXIOM in
;;; abelian-group.scm, so views.scm saw it at def-functor time and built
;;; abelian-group-idempotent-is-id-module-vector-ag for free.  Now that it is
;;; PROVED above -- three hundred files later in the load -- that companion has
;;; to be built here, or theorem-library/module-zero-act, which cites it by
;;; name, loses it.  Moving a fact from the axiom shelf to the theorem shelf
;;; moves it past the specializer.
;;;
;;; RESTRICTED to that one theorem on purpose: the unrestricted re-run installs
;;; 67 companions here (every abelian-group theorem proved since views.scm), all
;;; sound and all but one unasked for.  The line above it is unrestricted for
;;; the historical reason that its whole point is to carry ag-cancel-right and
;;; whatever else the ring view has been missing.
(view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-idempotent-is-id)

;;; ... and transport! takes THAT to the integers, in the surface language:
;;;     forall a,b,c in ZZ. a + c = b + c => a = b
(transport! 'ag-cancel-right-ring-additive-ag 'ZZ-RING 'zz-is-ring 'zz-add-cancel)
(transport! 'ag-cancel-right-ring-additive-ag 'QQ-RING 'qq-is-ring 'qq-add-cancel)

;;; =======================================================================
;;; nn-add-cancel : the naturals, by restriction.  NN <= ZZ, and NN's + IS ZZ's.
;;; No induction, no Peano recursion -- the fact was never NN's to begin with.
(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (FORALL c (IMPLIES (IN c NN)
                     (IMPLIES (= (+ a c) (+ b c)) (= a b))))))))))
(di)(di)(di)(di)(di)(di)(di)
(fact 'nn-subset-zz 'a)
(fact 'nn-subset-zz 'b)
(fact 'nn-subset-zz 'c)
(fact 'zz-add-cancel 'a 'b 'c)
(ass)
(cn-qed! 'nn-add-cancel)
