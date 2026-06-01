;;; extended-reals.scm -- the extended real line RR* = [-inf, +inf]
;;;
;;; notes-16 step 6.  Per the user's intent, this is intentionally minimal:
;;; just the carrier class RR*, the two new constants POS-INF and NEG-INF,
;;; and the obvious ordering (NEG-INF is least, POS-INF is greatest).
;;;
;;; Arithmetic on the extended reals is NOT provided.  The standard pitfalls
;;; (POS-INF + NEG-INF, POS-INF - POS-INF, 0 * POS-INF, ...) are deliberately
;;; left out of scope; this file gives you RR* as an ordered carrier and
;;; nothing more.
;;;
;;; Conventions:
;;;   POS-INF, NEG-INF  -- opaque constants; just fresh symbols
;;;   RR*               -- proper class; characterised by rr-star-membership
;;;   RR subset RR*     -- derives from rr-star-membership; stated as a
;;;                        named theorem for direct use.
;;;
;;; The symbol RR* contains an asterisk; MIT Scheme accepts it as a
;;; single symbol.  The infix parser will not parse it from a string;
;;; use the raw S-expression form `'RR*` directly when constructing wffs.

;;; -----------------------------------------------------------------------
;;; Membership characterisation
;;;
;;; x in RR* iff x is a real, or x = POS-INF, or x = NEG-INF.

(theory-add-axiom! *current-theory* 'rr-star-membership
  '(FORALL x
      (IFF (IN x RR*)
           (OR (IN x RR)
               (OR (= x POS-INF) (= x NEG-INF))))))

;;; Convenience: RR subset RR* (immediate from the iff above).
;;; Stated as a named axiom so the user does not have to peel the iff each
;;; time; future work may demote to a derived theorem.
(theory-add-axiom! *current-theory* 'rr-subset-rr-star
  '(SUBSET RR RR*))

;;; The infinities are in RR* (also immediate from rr-star-membership).
(theory-add-axiom! *current-theory* 'pos-inf-in-rr-star
  '(IN POS-INF RR*))

(theory-add-axiom! *current-theory* 'neg-inf-in-rr-star
  '(IN NEG-INF RR*))

;;; -----------------------------------------------------------------------
;;; Distinctness
;;;
;;; The two infinities are distinct from each other and from any real
;;; number.  Without these, the membership iff would be vacuously
;;; satisfied even if POS-INF happened to coincide with, say, 0.

(theory-add-axiom! *current-theory* 'pos-inf-neq-neg-inf
  '(NOT (= POS-INF NEG-INF)))

(theory-add-axiom! *current-theory* 'pos-inf-not-in-rr
  '(NOT (IN POS-INF RR)))

(theory-add-axiom! *current-theory* 'neg-inf-not-in-rr
  '(NOT (IN NEG-INF RR)))

;;; -----------------------------------------------------------------------
;;; Ordering
;;;
;;; POS-INF is the greatest element of RR*; NEG-INF is the least.
;;; The existing <= on RR is reused -- we just extend it to the two new
;;; points.  Reflexivity at POS-INF and NEG-INF follows by substituting
;;; x := POS-INF (or NEG-INF) in their respective bounds.

(theory-add-axiom! *current-theory* 'pos-inf-upper-bound
  '(FORALL x (IMPLIES (IN x RR*) (<= x POS-INF))))

(theory-add-axiom! *current-theory* 'neg-inf-lower-bound
  '(FORALL x (IMPLIES (IN x RR*) (<= NEG-INF x))))
