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

(add-axiom! *library* 'rr-star-membership
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

;;; neg-inf-not-in-rr RETIRED 2026-10-27 (stamp of 2026-09-18): proven modulo 0 in
;;; theorem-library/rr-star-order-minimal.scm, from neg-inf-lower-bound and RR arithmetic
;;; (EXT-ORDER, 2026-10-26).

;;; -----------------------------------------------------------------------
;;; Ordering
;;;
;;; POS-INF is the greatest element of RR-STAR; NEG-INF is the least.
;;; The existing <= on RR is reused -- we just extend it to the two new
;;; points.  Reflexivity at POS-INF and NEG-INF follows by substituting
;;; x := POS-INF (or NEG-INF) in their respective bounds.

;;; Both PRIMITIVE by the user's decision of 2026-09-18 (evening session) (see the note at the end of the file).
(fluid-let ((*current-provenance* 'primitive))
  (add-axiom! *library* 'pos-inf-upper-bound
    '(FORALL x (IMPLIES (IN x RR-STAR) (<= x POS-INF))))

  (add-axiom! *library* 'neg-inf-lower-bound
    '(FORALL x (IMPLIES (IN x RR-STAR) (<= NEG-INF x)))))

;;; THE ORDER PRIMITIVES OF THE EXT-ORDER WAVE (scratchpad/extorder/rr-star-order.scm,
;;; 2026-10-26; wired 2026-10-27 with the MINIMAL set only: rr-star-leq-antisymmetric and
;;; rr-star-leq-domain.  rr-star-leq-reflexive, -transitive and -total are NOT stamped: they are
;;; THEOREMS of theorem-library/rr-star-order-minimal.scm, EXT-ORDER item 5).
;;;
;;; <= IS A TOTAL ORDER ON RR-STAR, AND HOLDS ONLY THERE (the user's decisions, 2026-10-26:
;;; "<= is a total order on RR-STAR"; and "a <= b is FALSE if either a or b is not in
;;; RR-STAR").
;;;
;;; WHY THESE ARE AXIOMS.  `<=' is primitive.  The order axioms of number-systems.scm
;;; (rr-leq-reflexive, -antisymmetric, -transitive, -total) are guarded on membership in RR,
;;; because number-systems.scm loads long before RR-STAR exists; they say nothing about a
;;; comparison with POS-INF or NEG-INF.  The extended-reals axioms above (the two bounds and,
;;; until 2026-10-27, the stamp pos-inf-above-reals) decide every comparison between a real and an infinity, and an
;;; infinity with itself, but NOT the comparison POS-INF <= NEG-INF: the two-point extension
;;; of the ordered reals with the single extra pair POS-INF <= NEG-INF satisfies every axiom
;;; of this file before this block, and in it <= is neither antisymmetric (POS-INF <=
;;; NEG-INF <= POS-INF, POS-INF /= NEG-INF) nor transitive (POS-INF <= NEG-INF <= 0, NOT
;;; POS-INF <= 0) on RR-STAR (EXT-INF finding G1, 2026-10-26).  Nothing in the tree said
;;; either what <= does off RR-STAR.
;;;
;;; WHAT THE STAMP CLAIMS.  `primitive' contributes {} to every bill.  The claim is that
;;; this is part of what `<=' MEANS: the order of the extended real line, total on RR-STAR,
;;; and false whenever an argument lies outside it.  The rr-leq-* axioms on RR stay as they
;;; are; they are now special cases (proven as corollaries under -via-star names,
;;; theorem-library/rr-star-order-thms.scm).
;;;
;;; CONSISTENCY.  The intended model -- <= interpreted as the usual order of
;;; RR u {NEG-INF, POS-INF}, and false on every other pair -- satisfies the five order laws
;;; proposed by EXT-ORDER (the two stamped here and the three proven) and every
;;; primitive of the tree that mentions <= (safety scan, scratchpad/triage/EXT-ORDER-REPORT.md:
;;; 33 primitive axioms mention an order head, none concludes <= on a term not forced into
;;; RR-STAR; no asserted fact mentions <=; the oracles certify <= only between terms
;;; certified real or ground numerals).  Consistency is relative to NBG, as always.
;;;
;;; WHAT THEY BUY, AND WHAT IS REDUNDANT.  pos-inf-above-reals and neg-inf-not-in-rr (the
;;; 2026-09-18 stamps) and neg-inf-below-reals (proposed 2026-10-26) become THEOREMS
;;; (theorem-library/rr-star-order-minimal.scm), and so do rr-star-leq-reflexive,
;;; -transitive and -total: the minimal primitive set is rr-star-leq-antisymmetric with the
;;; two bounds (and rr-star-leq-domain, which nothing else yields).  With rr-star-leq-domain
;;; the RR-STAR guards of rr-star-leq-antisymmetric and rr-star-leq-transitive are implied
;;; by their <= antecedents; those of rr-star-leq-reflexive, rr-star-leq-total and the two
;;; bounds are not.  The guards are kept as decided.
(fluid-let ((*current-provenance* 'primitive))
  (add-axiom! *library* 'rr-star-leq-antisymmetric
    '(FORALL a (FORALL b
        (IMPLIES (AND (IN a RR-STAR) (IN b RR-STAR))
                 (IMPLIES (AND (<= a b) (<= b a)) (= a b))))))

  (add-axiom! *library* 'rr-star-leq-domain
    '(FORALL a (FORALL b
        (IMPLIES (<= a b) (AND (IN a RR-STAR) (IN b RR-STAR)))))))

;;; pos-inf-above-reals RETIRED 2026-10-27 (primitive by the user's decision of 2026-09-18:
;;; "POS-INF is +oo, so it has to be assumed as an axiom").  It is proven modulo 0 in
;;; theorem-library/rr-star-order-minimal.scm from rr-star-leq-antisymmetric and the two bounds
;;; (EXT-ORDER, 2026-10-26): POS-INF <= x <= POS-INF gives x = POS-INF, so POS-INF would be real,
;;; and POS-INF + 1 <= POS-INF is refuted by ineq.  The 2026-09-18 note "nothing in the tree can
;;; derive it" ceased to hold once antisymmetry on RR-STAR was decided (2026-10-26).

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
;;;
;;; THE 2026-10-27 STATE (EXT-ORDER, 2026-10-26; the user's decisions of that day).  The two
;;; 2026-09-18 stamps `neg-inf-not-in-rr' and `pos-inf-above-reals' are RETIRED: both are
;;; theorems of theorem-library/rr-star-order-minimal.scm, as is `neg-inf-below-reals', the
;;; mirror the note above says is missing.  The arguments above for `pos-inf-not-in-rr' and
;;; `pos-inf-neq-neg-inf' (rake-infinity-points.scm) now cite the THEOREM pos-inf-above-reals.
;;; What this file still assumes about the two points and the order: `rr-star-membership'
;;; (definitional) and the four primitives `pos-inf-upper-bound', `neg-inf-lower-bound',
;;; `rr-star-leq-antisymmetric' and `rr-star-leq-domain'.  Each is independent of the other
;;; three (models in scratchpad/triage/EXT-ORDER-REPORT.md, "Independence").
