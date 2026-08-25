;;; basic-rings.scm -- "officialize" NN/ZZ/QQ/RR/CC as algebraic structures
;;;
;;; The basic numeric domains use n-ary arithmetic operators (+ x y z),
;;; (* a b c d), etc. -- the form we learned in elementary school.  The
;;; RING and COMM-MONOID structures, on the other hand, require BINARY
;;; operations: an element of FUN(CARTESIAN(A, A), A).  This file is the
;;; bridge.
;;;
;;; The polymorphic binary operators binplus, bintimes, binneg are defined
;;; by extensional apply axioms; their values are the n-ary operations
;;; restricted to 2 (resp. 1) arguments.  They are typed separately for
;;; each domain D in {NN, ZZ, QQ, RR, CC} (binneg only for the rings, not
;;; for NN, since NN is not closed under negation).
;;;
;;; The instances ZZ-RING, QQ-RING, RR-NORMED-FIELD, CC-NORMED-FIELD are 6-element VNB
;;; lists [D, binplus, bintimes, binneg, 0, 1] -- the standard ring shape.
;;; IS-RING(ZZ-RING) and IS-RING(QQ-RING) used to be taken as axioms here, on
;;; the grounds that "proof would unfold IS-RING via the def-structure IFF and
;;; discharge each conjunct from typing axioms".  That is exactly what
;;; theorem-library/zz-ring-is-ring.scm now does, for both, from one
;;; parameterised driver -- so they are PROVEN and are not asserted below.
;;;
;;; NN-ADD-MONOID = [NN, binplus, 0] gives NN its commutative-monoid status
;;; under addition.  NN as a multiplicative comm-monoid is left for later.
;;;
;;; After loading this file, `specialize-structure` can transport every
;;; generic ring/comm-monoid theorem to the basic-domain instances:
;;;   (specialize-structure 'ZZ-RING 'RING 'zz-is-ring)
;;; brings `ring-add-comm[ZZ-RING]`, `ring-mul-assoc[ZZ-RING]`, etc.

;;; -----------------------------------------------------------------------
;;; Polymorphic binary operators (apply axioms)
;;;
;;; binplus(x, y)  = x + y
;;; bintimes(x, y) = x * y
;;; binneg(x)      = - x
;;;
;;; Stated extensionally rather than via VNB-LAMBDA, to avoid invoking the
;;; lambda-beta machinery on every reduction.  Each apply axiom is
;;; unconditional in the variables, matching the totality of the n-ary
;;; operations.

;; These three are the DEFINING equations of the primitive bridge symbols
;; binplus / bintimes / binneg -- each introduces a fresh symbol by an
;; equation, a conservative definitional extension.  Marked `definitional'
;; (not the bare `asserted' default): there is nothing above them to prove
;; FROM, so they are not warrant candidates.
(fluid-let ((*current-provenance* 'definitional))
 (theory-add-axiom! *current-theory* 'binplus-apply
   '(FORALL x (FORALL y (== (binplus x y) (+ x y)))))

 (theory-add-axiom! *current-theory* 'bintimes-apply
   '(FORALL x (FORALL y (== (bintimes x y) (* x y)))))

 (theory-add-axiom! *current-theory* 'binneg-apply
   '(FORALL x (== (binneg x) (- x)))))

;;; -----------------------------------------------------------------------
;;; Typing axioms per domain
;;;
;;; binplus, bintimes are typed for all 5 numeric domains.
;;; binneg is typed for the 4 ring domains (ZZ, QQ, RR, CC), not for NN.

(theory-add-axiom! *current-theory* 'binplus-in-fun-nn
  '(IN binplus (FUN (CARTESIAN NN NN) NN)))
(theory-add-axiom! *current-theory* 'binplus-in-fun-zz
  '(IN binplus (FUN (CARTESIAN ZZ ZZ) ZZ)))
(theory-add-axiom! *current-theory* 'binplus-in-fun-qq
  '(IN binplus (FUN (CARTESIAN QQ QQ) QQ)))
(theory-add-axiom! *current-theory* 'binplus-in-fun-rr
  '(IN binplus (FUN (CARTESIAN RR RR) RR)))
(theory-add-axiom! *current-theory* 'binplus-in-fun-cc
  '(IN binplus (FUN (CARTESIAN CC CC) CC)))

(theory-add-axiom! *current-theory* 'bintimes-in-fun-nn
  '(IN bintimes (FUN (CARTESIAN NN NN) NN)))
(theory-add-axiom! *current-theory* 'bintimes-in-fun-zz
  '(IN bintimes (FUN (CARTESIAN ZZ ZZ) ZZ)))
(theory-add-axiom! *current-theory* 'bintimes-in-fun-qq
  '(IN bintimes (FUN (CARTESIAN QQ QQ) QQ)))
(theory-add-axiom! *current-theory* 'bintimes-in-fun-rr
  '(IN bintimes (FUN (CARTESIAN RR RR) RR)))
(theory-add-axiom! *current-theory* 'bintimes-in-fun-cc
  '(IN bintimes (FUN (CARTESIAN CC CC) CC)))

(theory-add-axiom! *current-theory* 'binneg-in-fun-zz
  '(IN binneg (FUN ZZ ZZ)))
(theory-add-axiom! *current-theory* 'binneg-in-fun-qq
  '(IN binneg (FUN QQ QQ)))
(theory-add-axiom! *current-theory* 'binneg-in-fun-rr
  '(IN binneg (FUN RR RR)))
(theory-add-axiom! *current-theory* 'binneg-in-fun-cc
  '(IN binneg (FUN CC CC)))

;;; The typing axioms above are CLOSURE facts about the primitive numeric
;;; domains (e.g. CC is closed under negation).  Closure of a domain under
;;; its operations is not tactic-derivable here -- `(IN <expr> D)' does not
;;; compose through fun-apply-type (the known numeric-closure gap).  So these
;;; are genuine asserted content; warrant them `well-known' rather than leave
;;; them as unexamined `asserted' defaults in the warrant-candidate bucket.
(for-each
 (lambda (n) (warrant! n 'well-known
   "Closure of a primitive numeric domain under its arithmetic operation; standard."))
 '(binplus-in-fun-nn binplus-in-fun-zz binplus-in-fun-qq binplus-in-fun-rr binplus-in-fun-cc
   bintimes-in-fun-nn bintimes-in-fun-zz bintimes-in-fun-qq bintimes-in-fun-rr bintimes-in-fun-cc
   binneg-in-fun-zz binneg-in-fun-qq binneg-in-fun-rr binneg-in-fun-cc))

;;; -----------------------------------------------------------------------
;;; n-ary surface form -> nested binary bridge
;;;
;;; The parser emits flat n-ary nodes for chained + and *:
;;;   x + y + z       ->  (+ x y z)         (parser.scm p-parse-add)
;;;   a * b * c * d   ->  (* a b c d)       (parser.scm p-parse-mul)
;;; Binary - and unary - stay binary / unary:
;;;   x - y           ->  (- x y)
;;;   -x              ->  (- x)
;;; Algebraic structures (RING, COMM-MONOID, ...) use the binary slot ops
;;; binplus / bintimes / binneg.  These axioms rewrite the n-ary surface
;;; form to left-folded nested binary applications, matching the accumulator
;;; shape used by SUM-AG's recursion ((SUM-AG ag f (succ n)) = (OPR ag)(SUM-AG
;;; ag f n)(f n)) so the same fold direction lets downstream macetes line up.
;;;
;;; Arity 2 is just binplus-apply / bintimes-apply reversed, listed for
;;; uniformity.  Arities 3..5 cover the kid-friendly cases (granddaughters
;;; doing arithmetic).  Add higher arities when needed.
;;;
;;; PROVENANCE (2026-08-10, the user's call).  The three arity-2/arity-1 forms
;;; -- nary-plus-2, nary-times-2, nary-neg-1 -- are `definitional', and each is
;;; wrapped individually below rather than as a block, because they are not
;;; contiguous and reordering the file to make them so would cost more than it
;;; saves.  The reason they are definitional is exactly the comment above: each
;;; is the CONVERSE, written out, of binplus-apply / bintimes-apply /
;;; binneg-apply, which sit forty lines above stamped `definitional' as the
;;; defining equations of the bridge symbols.  `==' is quasi-equality, which is
;;; symmetric, so the converse of a conservative definition introduces nothing
;;; and owes nothing.  Until now they were `asserted' with no `warrant!', i.e.
;;; `trust: none' -- and being cited by the arithmetic layer they were, between
;;; them, the largest remaining source of that tier in the library.
;;;
;;; The wrap is what makes install-theorem! stamp the auto-generated `-rev'
;;; companion too, which a later register-provenance! would miss.
;;;
;;; nary-minus-2 is also `definitional' as of the same day, but on a DIFFERENT
;;; argument -- composition rather than symmetry -- so it carries its own note
;;; at its own definition below.
;;;
;;; NOT covered by any of this, and deliberately left `asserted': the arity 3-5
;;; forms, which are not converses of anything -- they FIX the reading of the
;;; parser's flat n-ary node as a left fold, and nothing else in the theory
;;; states it.  They have no dependents, so nothing is waiting on them.

(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'nary-plus-2
    '(FORALL x (FORALL y
        (== (+ x y) (binplus x y))))))

(theory-add-axiom! *current-theory* 'nary-plus-3
  '(FORALL x (FORALL y (FORALL z
      (== (+ x y z) (binplus (binplus x y) z))))))

(theory-add-axiom! *current-theory* 'nary-plus-4
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (== (+ w x y z) (binplus (binplus (binplus w x) y) z)))))))

(theory-add-axiom! *current-theory* 'nary-plus-5
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (== (+ v w x y z)
         (binplus (binplus (binplus (binplus v w) x) y) z))))))))

;; definitional: the converse of bintimes-apply (see the block comment above).
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'nary-times-2
    '(FORALL x (FORALL y
        (== (* x y) (bintimes x y))))))

(theory-add-axiom! *current-theory* 'nary-times-3
  '(FORALL x (FORALL y (FORALL z
      (== (* x y z) (bintimes (bintimes x y) z))))))

(theory-add-axiom! *current-theory* 'nary-times-4
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (== (* w x y z) (bintimes (bintimes (bintimes w x) y) z)))))))

(theory-add-axiom! *current-theory* 'nary-times-5
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (== (* v w x y z)
         (bintimes (bintimes (bintimes (bintimes v w) x) y) z))))))))

;;; Unary - (negation) and binary - (subtraction).
;;; The parser produces (- x) for unary and (- x y) for binary; chained
;;; subtraction like x - y - z left-associates to (- (- x y) z), so a single
;;; binary axiom handles it after iterated rewriting.

;; definitional: the converse of binneg-apply (see the block comment above).
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'nary-neg-1
    '(FORALL x
        (== (- x) (binneg x)))))

;; definitional, but NOT as a converse -- as a COMPOSITION of three definitions:
;;   (- x y)  ==  x + (- y)          binary-minus-def   (number-systems.scm)
;;            ==  binplus x (- y)    nary-plus-2        (above)
;;            ==  binplus x (binneg y)   nary-neg-1     (above)
;; `==' is a congruence, so the chain substitutes; each step is definitional, so
;; the composite introduces nothing.  Recorded separately because the argument is
;; a different one and was taken as a separate decision (2026-08-10, the user's
;; call): a converse is free by symmetry alone, whereas this one leans on
;; binary-minus-def actually BEING the definition of binary minus -- which it is,
;; and which nothing else in the theory states (see CLAUDE.md on binary minus
;; having had no axiom at all until 2026-08-01).
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'nary-minus-2
    '(FORALL x (FORALL y
        (== (- x y) (binplus x (binneg y)))))))

;;; -----------------------------------------------------------------------
;;; Ring instances: ZZ, QQ, RR, CC as RING
;;;
;;; Each is a 6-element VNB list [A, ADD, MUL, NEG, ZERO, ONE]:
;;;   A    = the carrier (NN/ZZ/QQ/RR/CC)
;;;   ADD  = binplus
;;;   MUL  = bintimes
;;;   NEG  = binneg
;;;   ZERO = 0
;;;   ONE  = 1
;;;
;;; Accessor reductions (e.g. (ADD ZZ-RING) -> (NTH 2 ZZ-RING)) are
;;; available via the def-structure machinery; combined with the LIST
;;; constructor + nth-reduce, (ADD ZZ-RING) computes down to binplus.

;;; declare-instance! installs the tuple equation under the SAME name it always
;;; had (zz-ring-def), and additionally the per-slot value macetes that let
;;; `slot' answer (MUL ZZ-RING) with bintimes in one step instead of exposing
;;; (NTH 3 ZZ-RING).  It also checks the tuple against the shape: a 7-tuple
;;; declared RING now fails the load rather than asserting a false IS-RING.
(declare-instance! 'ZZ-RING 'RING 'zz-ring-def
  '(ZZ binplus bintimes binneg 0 1))

(declare-instance! 'QQ-RING 'RING 'qq-ring-def
  '(QQ binplus bintimes binneg 0 1))

;;; RR-NORMED-FIELD and CC-NORMED-FIELD are 7-tuples carrying the structural norm at slot 7
;;; (NORMED-FIELD layout).  Slots 1..6 share RING's accessor indices, but a
;;; 7-tuple does NOT satisfy the length-6 predicates IS-RING / IS-COMMUTATIVE-
;;; RING / IS-INTEGRAL-DOMAIN (each pins length(s)=6).  Asserting those here
;;; was a flat inconsistency (length 6 = length 7); fixed 2026-05-30.  RR/CC
;;; reach the ring world via the NORMED-FIELD-AS-{COMMUTATIVE-RING,INTEGRAL-
;;; DOMAIN} view-as projections (views.scm), which build a fresh 6-tuple from
;;; slots 1..6 -- exactly how FIELD reaches it (FIELD-AS-INTEGRAL-DOMAIN).
;;;
;;; THE SAME MISTAKE CAME BACK SOMEWHERE ELSE, and stood for months: fixing it
;;; HERE fixed only the axioms stated here.  normed-vector-space.scm declared
;;; `(substructure SCAL RING)' -- which puts (IS-RING (SCAL s)) in the generated
;;; IFF, pinning length(SCAL s) = 6 -- and then pinned `scal(s) = rr-normed-field'
;;; by law, i.e. asserted 6 = 7 about a 7-tuple declared right here.  The
;;; predicate was UNSATISFIABLE and every theorem over it vacuous, from 2026-05-30
;;; until 2026-08-23.  Nothing caught it: the two halves are in another file and
;;; fourteen lines apart, and a vacuous hypothesis looks exactly like a good one.
;;; The standing check is now a must-not-prove entry (test-suite-negative.scm,
;;; section 2c): `IS-NORMED-VECTOR-SPACE(s) |- falsity' must be REFUSED.  Any
;;; future structure whose slot holds one of these 7-tuples wants the same entry.
(declare-instance! 'RR-NORMED-FIELD 'NORMED-FIELD 'rr-normed-field-def
  '(RR binplus bintimes binneg 0 1 abs))

(declare-instance! 'CC-NORMED-FIELD 'NORMED-FIELD 'cc-normed-field-def
  '(CC binplus bintimes binneg 0 1 magnitude))

;;; IS-X witnesses, taken as axioms (each true of the domain; no proofs).
;;; CRITICAL: a structure predicate IS-X bakes in length(s)=n, so a tuple can
;;; only witness predicates of its OWN shape.
;;;   ZZ-RING, QQ-RING : 6-tuples -> RING / COMMUTATIVE-RING / INTEGRAL-DOMAIN
;;;                      (and ZZ also EUCLIDEAN-RING; all 6-slot).
;;;   RR-NORMED-FIELD, CC-NORMED-FIELD : 7-tuples (NORMED-FIELD shape) -> IS-NORMED-FIELD only;
;;;                      ring structure via the NORMED-FIELD-AS-* views.
;;;   QQ as a FIELD     : the separate 8-tuple QQ-FIELD below (FIELD is 8-slot).

;;; zz-is-ring is NOT an axiom any more: it is PROVED, in
;;; theorem-library/zz-ring-is-ring.scm, from the tuple definition, the three
;;; operation typings and the arithmetic laws below -- which is what it always
;;; was, mathematically.  As an assertion it was billed against every theorem
;;; that reached the integers through their ring structure.
;;; qq-is-ring is NOT asserted here.  PROVEN, alongside zz-is-ring and by the
;;; same parameterised driver, in theorem-library/zz-ring-is-ring.scm: QQ-RING
;;; is the same tuple over a different carrier, so the instance data (carrier,
;;; defining equation, set-hood fact, three typing axioms) is all that differs.

;;; zz-is-commutative-ring and zz-is-integral-domain are NOT asserted here.
;;; Both are PROVEN in theorem-library/zz-integral-domain.scm, which unfolds the
;;; defining IFF, drops to the surface language, and gets ZZ's lack of zero
;;; divisors from QQ having inverses.  They were asserted and unwarranted until
;;; 2026-08-10, and zz-is-integral-domain was then the largest single source of
;;; `trust: none' in the library (seven bills, shadowing every other leaf in
;;; them).  zz-is-euclidean-ring is still asserted: it needs the DIVISION
;;; algorithm on ZZ, which is a different piece of work.
(theory-add-axiom! *current-theory* 'zz-is-euclidean-ring   '(IS-EUCLIDEAN-RING ZZ-RING))

(theory-add-axiom! *current-theory* 'qq-is-commutative-ring '(IS-COMMUTATIVE-RING QQ-RING))
(theory-add-axiom! *current-theory* 'qq-is-integral-domain  '(IS-INTEGRAL-DOMAIN QQ-RING))

(theory-add-axiom! *current-theory* 'rr-is-normed-field     '(IS-NORMED-FIELD RR-NORMED-FIELD))
(theory-add-axiom! *current-theory* 'cc-is-normed-field     '(IS-NORMED-FIELD CC-NORMED-FIELD))

;;; WARRANTED 2026-08-24, not stamped.  `rr-is-normed-field' is the ONLY door
;;; to IS-COMMUTATIVE-RING at the reals -- RR reaches the ring world solely
;;; through NORMED-FIELD-AS-COMMUTATIVE-RING -- so every RR-as-a-ring statement
;;; in the library inherited it, and with NO warrant at all that meant every
;;; such bill read `trust: none': the weakest report there is, for what is
;;; simply the statement that the reals are a normed field.  Eleven bills, all
;;; of them, on the measurement of 2026-08-24.
;;;
;;; It is NOT stamped `definitional' or `primitive'.  Those say "this is not
;;; debt"; this IS debt -- a fact with a derivation nobody has run -- and the
;;; shelf is the user's decision, not a driver's.  `warrant!' says what the
;;; derivation is and leaves the obligation visible.
(warrant! 'rr-is-normed-field 'well-known
  "RR is a normed field under abs.  Eight of the nine conjuncts of the
   IS-NORMED-FIELD IFF are the field and order axioms of number-systems.scm,
   discharged exactly as theorem-library/zz-ring-is-ring.scm discharges the
   six-slot IS-RING for ZZ-RING and QQ-RING: unfold the defining IFF, drop the
   accessors to the surface operations (binplus/bintimes/binneg/0/1), and cite
   rr-add-assoc / rr-add-comm / rr-add-zero / rr-neg-inverse / rr-mul-assoc /
   rr-mul-comm / rr-one-mul / rr-distributive.  The ninth is is-norm(abs, ...),
   whose four value clauses are PROVEN, in theorem-library/rr-abs-basics.scm:
   rr-abs-nonneg (0 <= |a|), rr-abs-zero (|a| = 0 iff a = 0), rr-abs-mult
   (|ab| = |a||b|) and rr-abs-triangle (|a+b| <= |a| + |b|).

   TWO THINGS BLOCK THE MECHANIZATION, and neither is the mathematics.  (1)
   is-norm's FIRST conjunct is `abs in FUN(CARR, RR)' -- membership in a
   function SPACE, not the pointwise typing rr-abs-closed gives.  `abs' is a
   primitive operator, i.e. a class function; that its restriction to RR is a
   SET is a replacement/sethood obligation, and nothing in the tree states it
   for abs (nor for `magnitude', which puts cc-is-normed-field in exactly the
   same position).  (2) LOAD ORDER: rr-abs-basics.scm is a theorem-library file
   and loads some 900 entries after this one, so the proof cannot live where
   the axiom is cited from; retiring the axiom means moving the citation site,
   the way zz-is-integral-domain was moved.")
(topic! 'rr-is-normed-field 'algebra)

;;; -----------------------------------------------------------------------
;;; QQ as a field: the 8-tuple QQ-FIELD.
;;;
;;; FIELD is its own 8-slot shape [A ADD MUL NEG ZERO ONE NON-ZERO INV]
;;; (field.scm), so a field instance must be an 8-tuple -- QQ-RING (6) cannot
;;; witness IS-FIELD.  QQ-FIELD carries NON-ZERO = QQ minus {0} (matching
;;; field-non-zero-carrier) and INV = recip; recip's multiplicative-inverse
;;; law (qq-recip-inverse, number-systems.scm) underwrites field-mul-inverse.
(declare-instance! 'QQ-FIELD 'FIELD 'qq-field-def
  '(QQ binplus bintimes binneg 0 1
       (DIFFERENCE QQ (SINGLETON 0)) recip))

(theory-add-axiom! *current-theory* 'qq-field-is-field '(IS-FIELD QQ-FIELD))

;;; -----------------------------------------------------------------------
;;; RR-MS -- RR as a metric space, distance |x - y|.
;;;
;;; Mirrors CC-MS (complex.scm).  Completeness is asserted through the
;;; generic IS-COMPLETE predicate (metric-completeness.scm); the bespoke
;;; "rr-complete" the earlier design deferred is exactly IS-COMPLETE(RR-MS).

;; The tuple equation is a DEFINITION (def-constant, definitional, citable), not
;; an axiom: a theory-add-axiom! of it takes the default `asserted' provenance
;; and downgrades a definition to a phantom debt leaf.  rr-ms-def had this right
;; before the other instances did; declare-instance! now does it for all of them.
(declare-instance! 'RR-MS 'METRIC-SPACE 'rr-ms-def
  '(RR (VNB-LAMBDA (LIST x y) (CARTESIAN RR RR) (abs (- x y)))))

;; rr-is-metric-space MOVED 2026-08-16 to theorem-library/rr-metric-space-proof.scm,
;; where IS-METRIC-SPACE(RR-MS) is PROVEN `modulo 0'.  It was a bare
;; theory-add-axiom! here with NO warrant! at all -- so it billed `trust: none',
;; the weakest report there is, and it was the sole unwarranted leaf of
;; rr-complete.  The comment above used to end "...is an axiom (provable from the
;; abs axioms in number-systems.scm once FUN-typing of the lambda is in place)":
;; that typing is the MULTI-BINDER case of pi-lambda-type!, added 2026-08-14.
;; The one law the abs axioms do NOT give is symmetry, |u-v| = |v-u| -- see
;; rr-abs-neg in theorem-library/rr-order-basics.scm.

;; rr-complete MOVED 2026-08-02 to theorem-library/rr-complete-proof.scm, where
;; IS-COMPLETE(RR-MS) is PROVEN.  It was asserted here for as long as RR had no
;; completeness axiom to prove it from; rr-sup-in/-upper/-least (number-systems,
;; 2026-08-01) changed that, and this is their first real consumer.

;;; -----------------------------------------------------------------------
;;; NN as a commutative monoid under addition
;;;
;;; NN-ADD-MONOID = [NN, binplus, 0]
;;;
;;; NN is not a ring (no negation), but it is a commutative monoid under
;;; +, with identity 0.

(declare-instance! 'NN-ADD-MONOID 'COMM-MONOID 'nn-add-monoid-def
  '(NN binplus 0))

;;; nn-add-monoid-is-comm-monoid is NOT asserted here: PROVEN in
;;; theorem-library/nn-add-monoid.scm, by citing the NN axioms rather than by
;;; running a commutative-RING oracle over a carrier that is not a ring.
;;; Asserted and unwarranted until 2026-08-10.

;;; -----------------------------------------------------------------------
;;; Register the numeric instances as definitional structures so they
;;; appear in (known-structures), in the library index/manual, and as nodes
;;; in the structure-relationship graph with a solid `refines` edge to the
;;; deepest shape they witness.  Each is a concrete instance, not a new
;;; refining predicate; the parent is chosen as the deepest IS-X already
;;; asserted above.  ZZ stops at euclidean-ring (not a field).  RR and CC
;;; reach normed-field (norm = abs / magnitude, witnessed in number-systems).
;;; NN-ADD-MONOID is the additive comm-monoid only (NN as a multiplicative
;;; comm-monoid is deferred).

(register-definitional-structure! 'ZZ-RING        'EUCLIDEAN-RING)
(register-definitional-structure! 'QQ-RING        'INTEGRAL-DOMAIN)
(register-definitional-structure! 'QQ-FIELD       'FIELD)
(register-definitional-structure! 'RR-NORMED-FIELD        'NORMED-FIELD)
(register-definitional-structure! 'CC-NORMED-FIELD        'NORMED-FIELD)
(register-definitional-structure! 'NN-ADD-MONOID  'COMM-MONOID)

;;; -----------------------------------------------------------------------
;;; n-ary surface -> adult REDUCE bridge (parallel to nary-plus-N).
;;;
;;; Same kiddie surface (+ x_1 ... x_n), routed instead to
;;;   (REDUCE binplus (FAM-OF-LIST (LIST x_1 ... x_n)) n).
;;; Lets a proof that reaches for SUM-AG-style finite-sum machinery
;;; pick up the n-ary form via this rewrite, while proofs that work in
;;; nested binplus continue to use nary-plus-N above.  Consistency between
;;; the two routes is a consequence of reduce-one + reduce-succ +
;;; fam-of-list-apply + the kernel NTH rules (not asserted, follows by
;;; unfolding).

(theory-add-axiom! *current-theory* 'nary-plus-2-list
  '(FORALL x (FORALL y
      (== (+ x y) (REDUCE binplus (FAM-OF-LIST (LIST x y)) 2)))))

(theory-add-axiom! *current-theory* 'nary-plus-3-list
  '(FORALL x (FORALL y (FORALL z
      (== (+ x y z) (REDUCE binplus (FAM-OF-LIST (LIST x y z)) 3))))))

(theory-add-axiom! *current-theory* 'nary-plus-4-list
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (== (+ w x y z) (REDUCE binplus (FAM-OF-LIST (LIST w x y z)) 4)))))))

(theory-add-axiom! *current-theory* 'nary-plus-5-list
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (== (+ v w x y z)
         (REDUCE binplus (FAM-OF-LIST (LIST v w x y z)) 5))))))))

(theory-add-axiom! *current-theory* 'nary-times-2-list
  '(FORALL x (FORALL y
      (== (* x y) (REDUCE bintimes (FAM-OF-LIST (LIST x y)) 2)))))

(theory-add-axiom! *current-theory* 'nary-times-3-list
  '(FORALL x (FORALL y (FORALL z
      (== (* x y z) (REDUCE bintimes (FAM-OF-LIST (LIST x y z)) 3))))))

(theory-add-axiom! *current-theory* 'nary-times-4-list
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (== (* w x y z) (REDUCE bintimes (FAM-OF-LIST (LIST w x y z)) 4)))))))

(theory-add-axiom! *current-theory* 'nary-times-5-list
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (== (* v w x y z)
         (REDUCE bintimes (FAM-OF-LIST (LIST v w x y z)) 5))))))))
