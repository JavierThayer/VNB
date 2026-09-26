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
;;; rr-subset-rr-star RETIRED 2026-09-19: proven modulo 0 in theorem-library/rake-infinity-points.scm

;;; The infinities are in RR-STAR (also immediate from rr-star-membership).
;;; pos-inf-in-rr-star RETIRED 2026-09-19: proven modulo 0 in theorem-library/rake-infinity-points.scm

;;; neg-inf-in-rr-star RETIRED 2026-09-19: proven modulo 0 in theorem-library/rake-infinity-points.scm

;;; -----------------------------------------------------------------------
;;; Distinctness
;;;
;;; The two infinities are distinct from each other and from any real
;;; number.  Without these, the membership iff would be vacuously
;;; satisfied even if POS-INF happened to coincide with, say, 0.

;;; pos-inf-neq-neg-inf RETIRED 2026-09-19: proven modulo 0 in theorem-library/rake-infinity-points.scm

;;; pos-inf-not-in-rr RETIRED 2026-09-19: proven modulo 0 in theorem-library/rake-infinity-points.scm

;;; PRIMITIVE by the user's decision of 2026-09-18 (evening session) (see the note at the end of the file).
(fluid-let ((*current-provenance* 'primitive))
  (theory-add-axiom! *current-theory* 'neg-inf-not-in-rr
    '(NOT (IN NEG-INF RR))))

;;; -----------------------------------------------------------------------
;;; Ordering
;;;
;;; POS-INF is the greatest element of RR-STAR; NEG-INF is the least.
;;; The existing <= on RR is reused -- we just extend it to the two new
;;; points.  Reflexivity at POS-INF and NEG-INF follows by substituting
;;; x := POS-INF (or NEG-INF) in their respective bounds.

;;; Both PRIMITIVE by the user's decision of 2026-09-18 (evening session) (see the note at the end of the file).
(fluid-let ((*current-provenance* 'primitive))
  (theory-add-axiom! *current-theory* 'pos-inf-upper-bound
    '(FORALL x (IMPLIES (IN x RR-STAR) (<= x POS-INF))))

  (theory-add-axiom! *current-theory* 'neg-inf-lower-bound
    '(FORALL x (IMPLIES (IN x RR-STAR) (<= NEG-INF x)))))

;;; POS-INF IS STRICTLY ABOVE EVERY REAL (the user's decision, 2026-09-18: "POS-INF is
;;; +oo, so it has to be assumed as an axiom").
;;;
;;; WHY IT IS AN AXIOM AND NOT A THEOREM.  `pos-inf-upper-bound' says x <= POS-INF and
;;; nothing above says the converse fails.  `<=' is primitive, and the order axioms of
;;; number-systems.scm (reflexive, antisymmetric, transitive, total) are all guarded on
;;; membership in RR, so they say nothing about a comparison with POS-INF.  A model in
;;; which POS-INF <= x also holds for every real x satisfies every axiom of this file.
;;; Found independently by two rake agents (batch 5, W and T).
;;;
;;; WHAT THE STAMP CLAIMS.  `primitive' contributes {} to every bill.  The claim is
;;; that this is part of what the symbol POS-INF MEANS -- the greatest element of the
;;; extended line, distinct from and not below any real -- and not a fact owed an
;;; argument.  For the sibling axioms of this file see the note at its end.
;;;
;;; WHAT IT BUYS.  Antisymmetry and transitivity of `<=' on RR-POS-STAR become
;;; provable by cases, which is what makes ESUP -- hence ESUM, EINF, ELIMINF and
;;; INTEGRAL -- determined by its characterising axioms; and the (<=) half of
;;; esum-finite-iff-bounded is four citations from it.
(fluid-let ((*current-provenance* 'primitive))
  (theory-add-axiom! *current-theory* 'pos-inf-above-reals
    '(FORALL x (IMPLIES (IN x RR) (NOT (<= POS-INF x))))))

;;; -----------------------------------------------------------------------
;;; THE SIBLING INFINITY AXIOMS: the user's decision of 2026-09-18 (evening session).
;;;
;;; Put to the user: "the sibling infinity axioms (membership in RR-STAR, distinctness,
;;; not real, the two bounds): stamp `primitive', as `pos-inf-above-reals' was?"  Answer:
;;; yes.  The decision is applied to the THREE of the eight that nothing in the tree can
;;; derive, and the other five are left as debt to be PROVEN, following the order of
;;; preference of the library-build policy (define and prove; prove; only then a stamp).
;;;
;;; STAMPED `primitive' -- each says what a new point IS, and no axiom could yield it:
;;;   neg-inf-not-in-rr     NEG-INF is not a real.  (There is no `neg-inf-below-reals'
;;;                         mirror of `pos-inf-above-reals', so the argument that proves
;;;                         `pos-inf-not-in-rr' has no counterpart here.)
;;;   pos-inf-upper-bound   x <= POS-INF on RR-STAR.
;;;   neg-inf-lower-bound   NEG-INF <= x on RR-STAR.
;;; WHAT THE STAMP CLAIMS: that these are part of the meaning of the symbols POS-INF and
;;; NEG-INF (the greatest and least points of the extended line, NEG-INF not a real), so
;;; they contribute {} to every bill.  They are consistent with the rest of the file: the
;;; two-point extension of the ordered reals is a model.
;;;
;;; NOT STAMPED, because each is DERIVABLE, and PROVEN `modulo 0' the same evening
;;; (theorem-library/rake-infinity-points.scm; the five axiom forms above are retired):
;;;   rr-subset-rr-star, pos-inf-in-rr-star, neg-inf-in-rr-star
;;;                         -- each is one disjunct of `rr-star-membership';
;;;   pos-inf-not-in-rr     -- if POS-INF were real, `pos-inf-above-reals' at x := POS-INF
;;;                            would contradict reflexivity of <= on RR;
;;;   pos-inf-neq-neg-inf   -- if POS-INF = NEG-INF, `neg-inf-lower-bound' at x := 0 gives
;;;                            POS-INF <= 0, contradicting `pos-inf-above-reals'.
;;; What this file still assumes about the two points: `rr-star-membership'
;;; (definitional) and the four primitives `pos-inf-above-reals', `neg-inf-not-in-rr',
;;; `pos-inf-upper-bound', `neg-inf-lower-bound'.
