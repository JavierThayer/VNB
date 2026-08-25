;;; prove-scripts/drives/nvs-scalar-bridge-drive.scm
;;;
;;; ONE LEAF, LEFT OPEN ON PURPOSE, for you to drive.
;;;
;;; Run it:      ./prover -i prove-scripts/drives/nvs-scalar-bridge-drive.scm
;;;
;;; ====================================================================
;;; WHAT CHANGED SINCE THE LAST VERSION OF THIS FILE
;;; ====================================================================
;;;
;;; Two things, and the first is why the second is now worth doing.
;;;
;;; (1) IS-NORMED-VECTOR-SPACE IS NO LONGER UNSATISFIABLE.  It used to pin
;;;     `scal(s) = rr-normed-field' -- a SEVEN-tuple -- beside a
;;;     `(substructure SCAL RING)' clause that pins length(scal(s)) = 6, so the
;;;     predicate asserted 6 = 7 and every theorem over it was VACUOUS.  Since
;;;     2026-08-23 the scalars are pinned through the ring VIEW,
;;;         scal(s) = normed-field-as-commutative-ring(rr-normed-field)
;;;     which projects slots 1..6 into a fresh 6-tuple.  A theorem about a
;;;     normed vector space is now an ordinary unexemplified theorem, not a
;;;     vacuous one.  (scratchpad/nvs-falsity-probe.scm reports which of the two
;;;     states the tree is in, by measuring both length claims.)
;;;
;;; (2) THE SCALAR BRIDGE EXISTS AND IS PROVEN.  The last version of this file
;;;     said "Nothing in the tree does this today" and offered a three-move
;;;     guess at step 2, ending "IF STEP 2 FAILS, that is the finding".  Step 2
;;;     no longer needs guessing: theorem-library/normed-field-ring-view.scm
;;;     proves twelve read-offs of the view, all `modulo 0' --
;;;
;;;         rr-scalar-ring-carr : carr(normed-field-as-commutative-ring(
;;;                                     rr-normed-field)) == rr
;;;         rr-scalar-ring-add  : ... == binplus
;;;         rr-scalar-ring-mul  : ... == bintimes
;;;         rr-scalar-ring-neg  : ... == binneg
;;;         rr-scalar-ring-zero : ... == 0
;;;         rr-scalar-ring-one  : ... == 1
;;;
;;;     plus the six generic in the normed field.  Each is an unconditional
;;;     `==', hence a live macete, so `mac' fires it by name on a goal.
;;;
;;; ====================================================================
;;; WHAT THE LEAF IS
;;; ====================================================================
;;;
;;; theorem-library/directional-derivative.scm ASSERTS six one-line vector facts
;;; (nvs-act-in-vec, nvs-vadd-in-vec, nvs-act-scale-assoc, nvs-act-collect,
;;; nvs-act-zero, nvs-act-one), each warranted `reference' and each described in
;;; its own warrant as a module axiom read with the scalars spelled as reals.
;;; With the bridge in hand they are no longer assertions in waiting: the only
;;; thing between the structure's own unital law and `nvs-act-one' is
;;;
;;;         ONE(SCAL m) = 1
;;;
;;; and this script LANDS THAT, below, in three moves.  What is left for you is
;;; the composition: rewrite the literal 1 in the goal back into ONE(SCAL m) and
;;; close on the structure's unital law.
;;;
;;; If it closes, the other five are the same shape at a different accessor
;;; (rr-scalar-ring-mul for scale-assoc, rr-scalar-ring-add for collect,
;;; rr-scalar-ring-zero for act-zero, rr-scalar-ring-carr for the two typings),
;;; and six `reference' warrants in directional-derivative.scm become proofs.

(define (nsb-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 60)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; nvs-act-one, restricted to the y_ = the unital case: 1.x = x.
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
                 (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (= ((ACT m) 1 x_) x_)))))))
(di) (di)

;;; the defining IFF, unfolded and split to atoms.  Two conjuncts matter:
;;;   scal(m) = normed-field-as-commutative-ring(rr-normed-field)   (the pinning)
;;;   forall x_ in vec(m). (act(m))(one(scal(m)), x_) = x_          (unital)
(quietly (lambda ()
  (mac-h 'IS-NORMED-VECTOR-SPACE '(IS-NORMED-VECTOR-SPACE m))
  (nsb-split!)))

;;; THE BRIDGE, done for you -- this is the part that did not exist before.
;;; `subst' reaches (SCAL m) because it sits in ARGUMENT position of ONE; it
;;; would NOT reach it inside an operator such as (MUL (SCAL m)), which is the
;;; standing trap (CLAUDE.md, "subst cannot rewrite a term in OPERATOR position")
;;; and the reason the other five bridges want `mac'/`mac-h', not `subst'.
(have! '(= (ONE (SCAL m)) 1)
       (lambda ()
         (subst '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
         (mac 'rr-scalar-ring-one)
         (rfl)))

(newline)
(display ";;; ------------------------------------------------------------------")(newline)
(display ";;; IN CONTEXT NOW: one(scal(m)) = 1   <- the bridge, proven, landed")(newline)
(display ";;; GOAL:           ")(display (expression->string (dk-goal)))(newline)
(display ";;; open leaves:    ")(display (length (proof-open-leaves *ps*)))(newline)
(newline)
(display ";;; SUGGESTED DRIVE -- type these one at a time and watch:")(newline)
(newline)
(display ";;;   ;; 0. see what the unfold gave you")(newline)
(display ";;;   (for-each (lambda (u) (display (expression->string u)) (newline)) (dk-asms))")(newline)
(newline)
(display ";;;   ;; 1. peel the goal's binder and its typing")(newline)
(display ";;;   (di)")(newline)
(newline)
(display ";;;   ;; 2. turn the goal's literal 1 back into one(scal(m)).  `subst'")(newline)
(display ";;;   ;;    rewrites LEFT to RIGHT, so the equation has to point that way;")(newline)
(display ";;;   ;;    eq-sym is PROVEN (modulo 0) and turns the bridge around.")(newline)
(display ";;;   (fact 'eq-sym '(ONE (SCAL m)) 1)")(newline)
(display ";;;   (subst '(= 1 (ONE (SCAL m))))")(newline)
(newline)
(display ";;;   ;; 3. instantiate the structure's own unital law at x_ and close.")(newline)
(display ";;;   ;;    Find it by its CONSEQUENT, never by a symbol it contains --")(newline)
(display ";;;   ;;    the context holds four look-alike action laws.")(newline)
(display ";;;   (inst+ <the FORALL whose body is (act(m))(one(scal(m)), x_) = x_> 'x_)")(newline)
(display ";;;   (ass)")(newline)
(newline)
(display ";;; WHAT TO REPORT BACK.  If step 2 or 3 needs a move the copilot did")(newline)
(display ";;; not offer, that is worth more than the leaf: `what-now' should be")(newline)
(display ";;; naming the bridge macete on a goal that mentions ONE(SCAL m), and")(newline)
(display ";;; the lane that should have said so is the thing to fix.")(newline)
(display ";;; ------------------------------------------------------------------")(newline)
