;;; lambda-slot-apply.scm -- taking an operation SLOT down to the surface.
;;;
;;;     ((VNB-LAMBDA (LIST x_ y_) (CARTESIAN dm_ dm_) (+ x_ y_)) a_ b_)  ==  a_ + b_
;;;
;;; WHY THIS FILE EXISTS.  Until 2026-08-29 every numeric instance's ADD slot
;;; held the single shared constant `binplus', and `surface-goal!' / `transport!'
;;; reached the surface in two macete steps: the instance's slot equation
;;; (ADD ZZ-RING) == binplus, then `binplus-apply', binplus(a,b) == a + b.
;;;
;;; That shared constant was the inconsistency.  `IN f (FUN A ...)' pins
;;; DOM(f) = A exactly (library.scm:321, dom-of-fun library.scm:500), so one object
;;; asserted into the five numeric function classes proved NN = ZZ = QQ = RR = CC,
;;; and with cc-i-squared that gives 0 <= -1.  The slots now hold a tupled
;;; VNB-LAMBDA per instance -- a genuine set function with one domain -- and the
;;; second of those two steps had nothing left to fire on: `crs' met
;;; (vnb-lambda(...))(u,v) where it used to meet u + v, and every ring-law
;;; conjunct stopped closing.
;;;
;;; These three theorems are that second step, restored.  They are the
;;; `rr-ms-dist' shape (theorem-library/rr-ms-dist.scm) -- a GUARDED `=='
;;; application read-off for a lambda-valued slot -- and they are stated GENERIC
;;; IN THE CARRIER, so ONE theorem serves ZZ, QQ, RR, CC and NN rather than one
;;; per instance.  `dm_' is a plain universally quantified variable; nothing
;;; about the proof needs it to be a numeric domain.
;;;
;;; TWO TRAPS, both of which cost a run and both of which CLAUDE.md warns about:
;;;
;;;   * PEEL BEFORE BETA.  `lam-b' licenses the redex against the enclosing
;;;     binders but posts its obligation in the OUTER context, so a beta fired
;;;     before the guards are peeled owes `[a_, b_] in cartesian(dm_, dm_)' at a
;;;     node where a_ and b_ are still free -- an unprovable leaf that nothing
;;;     reports until qed.  Peeled first, the reduction owes nothing at all.
;;;   * The carrier variable is `dm_', not `A_'.  `A_' folds to `a_' and IS the
;;;     bound variable a_; the formula round-trips through the printer looking
;;;     perfectly sensible while saying something else entirely.
;;;
;;; Stated with `==' and GUARDED, for rr-ms-dist's reason: off the carrier the
;;; left-hand side is an application outside the lambda's domain -- undefined --
;;; while nothing says a_ + b_ is undefined there.  The guards are the hypothesis
;;; under which the equation was ever true, not a tax on the rewrite.

(define (lsa-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (lsa-peel!)
  (let lp ((n 8))
    (when (and (> n 0) (memq (car (lsa-goal)) '(FORALL IMPLIES)))
      (di) (lp (- n 1)))))

(define (lsa-prove-binop! name op)
  ;; dm_ MUST be quantified.  Left free it is not a schema variable, so the
  ;; installed macete matches only the literal symbol `dm_' and never fires on
  ;; ZZ or RR -- it proves, installs, reports nothing, and silently rewrites
  ;; nothing.  That cost a full load to find.
  (sp (make-wff (list 'FORALL 'dm_
        (forall-guarded '(a_ b_) '((IN a_ dm_) (IN b_ dm_))
          (list '== (list (list 'VNB-LAMBDA '(LIST x_ y_) '(CARTESIAN dm_ dm_)
                                (list op 'x_ 'y_))
                          'a_ 'b_)
                    (list op 'a_ 'b_))))))
  (lsa-peel!)
  (lam-b)
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "lambda-slot-apply: did not close" name (lsa-goal)))
  (qed name))

(define (lsa-prove-unop! name op)
  (sp (make-wff (list 'FORALL 'dm_
        (forall-guarded '(a_) '((IN a_ dm_))
          (list '== (list (list 'VNB-LAMBDA 'x_ 'dm_ (list op 'x_)) 'a_)
                    (list op 'a_))))))
  (lsa-peel!)
  (lam-b)
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "lambda-slot-apply: did not close" name (lsa-goal)))
  (qed name))

(lsa-prove-binop! 'lam-slot-add-apply '+)
(topic! 'lam-slot-add-apply 'algebra)

(lsa-prove-binop! 'lam-slot-mul-apply '*)
(topic! 'lam-slot-mul-apply 'algebra)

(lsa-prove-unop! 'lam-slot-neg-apply '-)
(topic! 'lam-slot-neg-apply 'algebra)
