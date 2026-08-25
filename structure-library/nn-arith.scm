;;; nn-arith.scm -- the recursion equations for + and * on NN.
;;;
;;; THE GAP.  number-systems.scm (:43-87) axiomatizes NN with `succ' (a kernel
;;; term-former), closure, and the COMMUTATIVE-MONOID-ish laws of + and * --
;;; comm, assoc, distrib, a+0 = a, 1*a = a.  It never connects the two: there is
;;; no equation anywhere in the tree relating `+' to `succ'.  Not `succ n = n+1',
;;; not `a + succ b = succ(a+b)', nothing.  So NN's arithmetic is Peano's only in
;;; name: `+' is an abstract commutative operation that happens to fix 0.
;;;
;;; It bites the moment you do induction.  (ni) builds its step goal by
;;; substituting the SYMBOLIC term (succ n) (primitive-inferences.scm:1020), and
;;; then nothing can move: `crs' treats (succ n) as an opaque generator (it is
;;; not a ring head), `arith' only evaluates GROUND numerals, and no lemma
;;; rewrites it.  Every induction over NN arithmetic in this library has so far
;;; dodged this by never needing to cross the succ/+ boundary.
;;;
;;; The two equations below are that connection.  They are the standard
;;; primitive-recursive definition of + and * -- Peano's, in the form every
;;; textbook gives -- and with them the rest is THEOREM, not assertion:
;;; succ n = n + 1, additive cancellation, 2*k /= 2*j+1, parity, even-square-
;;; implies-even (see theorem-library/nn-parity-proof.scm).  They are stated
;;; here rather than derived only because number-systems.scm introduces NN by
;;; axiom rather than constructing it.
;;;
;;; SINCE 2026-08-24 THE TWO ARE NO LONGER ON THE SAME FOOTING.  `nn-add-succ'
;;; is stamped `definitional' -- trusted base, contributing {} to every bill --
;;; by an explicit decision recorded in full at its own site below, INCLUDING
;;; what that stamp assumes beyond a definition.  `nn-mul-succ' remains an
;;; asserted, warranted support.  Read the block above `nn-add-succ' before
;;; extending the treatment to anything else in this file.
;;;
;;; NOT asserted, because they are derivable and are proved in nn-parity-proof:
;;;   succ injective on NN  -- ord-succ-injective + ord-succ-nn (ordinals.scm)
;;;   a * 0 = 0             -- distributivity + additive cancellation
;;;
;;; Loads after number-systems (NN, +, *, succ) and proof-debt (support/warrant!).

;;; =======================================================================
;;; nn-add-succ IS STAMPED `definitional' (2026-08-24, the user's decision),
;;; and this comment is the CLAIM that stamp makes.  It is written out because
;;; nothing downstream will ever say it again.
;;;
;;; WHAT THE STAMP DOES.  `definitional' provenance contributes {} to every
;;; bill (proof-debt.scm:12), exactly as `primitive' does.  The fact therefore
;;; disappears from every `proven modulo {...}' line and becomes invisible to
;;; the debt ledger.  That is not a better tier of DEBT -- which is all a
;;; `warrant!' buys -- it is the assertion that there is no debt here to
;;; record.  For the same reason the `warrant! 'reference' this axiom used to
;;; carry has been REMOVED rather than reworded, following the precedent of the
;;; 28 ordinal axioms (structure-library/ordinals.scm, 2026-07-27): a
;;; foundational fact is not debt, so it does not get a warrant.
;;;
;;; WHAT IS BEING ASSUMED.  Two things, not one.
;;;
;;;   (1) That `a + succ(b) = succ(a + b)' is the recursion equation DEFINING
;;;       addition on NN -- Peano's, in the form every textbook gives.  Asked
;;;       to justify it a mathematician answers "because that is what + on the
;;;       naturals IS", which is exactly the test the ordinal axioms and
;;;       `image-set' (structure-library/injection.scm) were admitted to the
;;;       trusted base by.
;;;
;;;   (2) -- AND THIS ONE IS A CLAIM, NOT A DEFINITION -- that the `+' this
;;;       equation constrains is the `+' the theory already has.
;;;       number-systems.scm (:43-87) introduces NN's addition by its
;;;       ALGEBRAIC laws (closure, associativity, commutativity, a + 0 = a)
;;;       and never by its recursion; `succ' is a kernel term-former
;;;       introduced separately, and no axiom in the tree relates the two.  So
;;;       calling this equation "definitional" also asserts that the
;;;       algebraically-axiomatised + SATISFIES the Peano recursion, i.e. that
;;;       the two presentations agree.  That agreement holds in the intended
;;;       model and is established nowhere in this tree.  This is therefore
;;;       NOT a conservative extension of what number-systems.scm states: it
;;;       is a further axiom about the symbol that file introduced, and the
;;;       stamp is what hides it from the bills.
;;;
;;; WHAT WOULD DISCHARGE IT.  Construct NN's `+' instead of axiomatising it.
;;; The facility is already here and already in use: `def-by-nn-recursion'
;;; (structure-library/ordinals.scm:334) defines FALLING (injection.scm:312)
;;; and MPOW (monoid-power.scm:25) by exactly this recursion on the second
;;; argument.  Define + that way, derive commutativity / associativity /
;;; a + 0 = a from that definition, and prove that the constructed operation
;;; AGREES with the one number-systems.scm posits.  At that point (1) is a definition in fact and
;;; (2) is a theorem, and this file can go back to an ordinary `support'.
;;; Until then the exit exists on paper only, and the assumption above is the
;;; price of the 20 bills the stamp clears.
;;;
;;; SCOPE.  This decision is about `nn-add-succ' ALONE.  `nn-mul-succ' below
;;; carries the identical argument and is DELIBERATELY LEFT asserted: one
;;; explicit decision per fact.  Growing the trusted base by analogy with a
;;; neighbouring decision is precisely how it stops being explicit.
;;;
;;; MEASURED 2026-08-24, over 719 proven results: the name was in 55 bills and
;;; was the SOLE unwarranted leaf of 20 of them; the stamp clears those 20 to
;;; `modulo 0' (cc-complete and rr-complete among them, and the whole
;;; deriv-/dyadic- block) and shortens 35 more.  `trust: none' does not move
;;; -- it stays at 3.  No bill grew.  `modulo 0' goes 448 -> 468.
;;;
;;; Note WHICH ranking made this the biggest leaf left, because the two are not
;;; the same and the citation count is the misleading one.  By citations it was
;;; only THIRD (55, behind entry-in-carrier's 63 and interval-card-in-nn's 60);
;;; by SOLE-leaf count it was first by half again -- 20, against 13 for
;;; rr-le-all-pos-nonpos and 8 for metric-dist-real -- and neither of the two
;;; more-cited leaves is EVER a bill's only one, so discharging either would
;;; have cleared nothing.  Triage by BILL, not by citation count.  After the
;;; stamp the sole-leaf ranking is headed by rr-le-all-pos-nonpos at 13.
;;;
;;; Two visible side effects, both expected.  `support' registers a PSS entry
;;; and load.scm de-supports every definitional-provenance entry, so the load's
;;; `classification:' line goes 17 -> 19 definitions de-supported -- TWO, not
;;; one, because the `fluid-let' also stamps the auto-generated `nn-add-succ-rev'
;;; companion, which is the whole reason for wrapping the install rather than
;;; re-stamping by name afterwards.  And the catalog moves one result from the
;;; support column to the definition column (577/605 -> 576/606).  The equation
;;; still fires as a rewrite in both directions: macete installation is a
;;; separate registry, untouched by the classification.
;;; =======================================================================

;;; a + succ(b) = succ(a + b)
(fluid-let ((*current-provenance* 'definitional))
  (support 'nn-add-succ
    '(FORALL a
       (IMPLIES (IN a NN)
         (FORALL b
           (IMPLIES (IN b NN)
             (= (+ a (succ b)) (succ (+ a b)))))))))

;;; a * succ(b) = a*b + a
(support 'nn-mul-succ
  '(FORALL a
     (IMPLIES (IN a NN)
       (FORALL b
         (IMPLIES (IN b NN)
           (= (* a (succ b)) (+ (* a b) a)))))))

(warrant! 'nn-mul-succ 'reference
  "The recursion equation defining * on NN: a * succ(b) = a*b + a.  Peano.
   Same gap as nn-add-succ: number-systems.scm gives * its algebraic laws and
   never relates it to succ.")
