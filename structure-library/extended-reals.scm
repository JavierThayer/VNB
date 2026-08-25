;;; extended-reals.scm -- the extended real line RR-STAR = [-inf, +inf]
;;;
;;; notes-16 step 6.  Per the user's intent, this is intentionally minimal:
;;; just the carrier class RR-STAR, the two new constants POS-INF and NEG-INF,
;;; and the obvious ordering (NEG-INF is least, POS-INF is greatest).
;;;
;;; Arithmetic on the extended reals is NOT provided.  The standard pitfalls
;;; (POS-INF + NEG-INF, POS-INF - POS-INF, 0 * POS-INF, ...) are deliberately
;;; left out of scope; this file gives you RR-STAR as an ordered carrier and
;;; nothing more.
;;;
;;; Conventions:
;;;   POS-INF, NEG-INF  -- opaque constants; just fresh symbols
;;;   RR-STAR               -- proper class; characterised by rr-star-membership
;;;   RR subset RR-STAR     -- derives from rr-star-membership; stated as a
;;;                        named theorem for direct use.
;;;
;;; The class was called RR* until 2026-08-24.  MIT Scheme read that as a
;;; single symbol, but the VNB tokenizer did not: `read-ident' stops at the
;;; `*' and `read-op' takes it, so "x in rr*" parsed as a PRODUCT and no
;;; formula about the extended reals could be retyped from its printed form.
;;; The name is now RR-STAR, which is what every axiom below already called
;;; it (rr-star-membership, pos-inf-in-rr-star, ...), and it parses.

;;; -----------------------------------------------------------------------
;;; Membership characterisation
;;;
;;; x in RR-STAR iff x is a real, or x = POS-INF, or x = NEG-INF.

(theory-add-axiom! *current-theory* 'rr-star-membership
  '(FORALL x
      (IFF (IN x RR-STAR)
           (OR (IN x RR)
               (OR (= x POS-INF) (= x NEG-INF))))))

;;; Convenience: RR subset RR-STAR (immediate from the iff above).
;;; Stated as a named axiom so the user does not have to peel the iff each
;;; time; future work may demote to a derived theorem.
(theory-add-axiom! *current-theory* 'rr-subset-rr-star
  '(SUBSET RR RR-STAR))

;;; The infinities are in RR-STAR (also immediate from rr-star-membership).
(theory-add-axiom! *current-theory* 'pos-inf-in-rr-star
  '(IN POS-INF RR-STAR))

(theory-add-axiom! *current-theory* 'neg-inf-in-rr-star
  '(IN NEG-INF RR-STAR))

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
;;; POS-INF is the greatest element of RR-STAR; NEG-INF is the least.
;;; The existing <= on RR is reused -- we just extend it to the two new
;;; points.  Reflexivity at POS-INF and NEG-INF follows by substituting
;;; x := POS-INF (or NEG-INF) in their respective bounds.

(theory-add-axiom! *current-theory* 'pos-inf-upper-bound
  '(FORALL x (IMPLIES (IN x RR-STAR) (<= x POS-INF))))

(theory-add-axiom! *current-theory* 'neg-inf-lower-bound
  '(FORALL x (IMPLIES (IN x RR-STAR) (<= NEG-INF x))))
