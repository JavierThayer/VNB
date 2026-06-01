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
;;; The instances ZZ-RING, QQ-RING, RR-RING, CC-RING are 6-element VNB
;;; lists [D, binplus, bintimes, binneg, 0, 1] -- the standard ring shape.
;;; IS-RING(*-RING) is taken as an axiom (proof would unfold IS-RING via
;;; the def-structure IFF and discharge each conjunct from typing axioms).
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

(theory-add-axiom! *current-theory* 'binplus-apply
  '(FORALL x (FORALL y (= (binplus x y) (+ x y)))))

(theory-add-axiom! *current-theory* 'bintimes-apply
  '(FORALL x (FORALL y (= (bintimes x y) (* x y)))))

(theory-add-axiom! *current-theory* 'binneg-apply
  '(FORALL x (= (binneg x) (- x))))

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
;;; shape used by SUM-AG's recursion ((SUM-AG ag f (succ n)) = (MUL ag)(SUM-AG
;;; ag f n)(f n)) so the same fold direction lets downstream macetes line up.
;;;
;;; Arity 2 is just binplus-apply / bintimes-apply reversed, listed for
;;; uniformity.  Arities 3..5 cover the kid-friendly cases (granddaughters
;;; doing arithmetic).  Add higher arities when needed.

(theory-add-axiom! *current-theory* 'nary-plus-2
  '(FORALL x (FORALL y
      (= (+ x y) (binplus x y)))))

(theory-add-axiom! *current-theory* 'nary-plus-3
  '(FORALL x (FORALL y (FORALL z
      (= (+ x y z) (binplus (binplus x y) z))))))

(theory-add-axiom! *current-theory* 'nary-plus-4
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (= (+ w x y z) (binplus (binplus (binplus w x) y) z)))))))

(theory-add-axiom! *current-theory* 'nary-plus-5
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (= (+ v w x y z)
         (binplus (binplus (binplus (binplus v w) x) y) z))))))))

(theory-add-axiom! *current-theory* 'nary-times-2
  '(FORALL x (FORALL y
      (= (* x y) (bintimes x y)))))

(theory-add-axiom! *current-theory* 'nary-times-3
  '(FORALL x (FORALL y (FORALL z
      (= (* x y z) (bintimes (bintimes x y) z))))))

(theory-add-axiom! *current-theory* 'nary-times-4
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (= (* w x y z) (bintimes (bintimes (bintimes w x) y) z)))))))

(theory-add-axiom! *current-theory* 'nary-times-5
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (= (* v w x y z)
         (bintimes (bintimes (bintimes (bintimes v w) x) y) z))))))))

;;; Unary - (negation) and binary - (subtraction).
;;; The parser produces (- x) for unary and (- x y) for binary; chained
;;; subtraction like x - y - z left-associates to (- (- x y) z), so a single
;;; binary axiom handles it after iterated rewriting.

(theory-add-axiom! *current-theory* 'nary-neg-1
  '(FORALL x
      (= (- x) (binneg x))))

(theory-add-axiom! *current-theory* 'nary-minus-2
  '(FORALL x (FORALL y
      (= (- x y) (binplus x (binneg y))))))

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

(theory-add-axiom! *current-theory* 'zz-ring-def
  '(= ZZ-RING (LIST ZZ binplus bintimes binneg 0 1)))

(theory-add-axiom! *current-theory* 'qq-ring-def
  '(= QQ-RING (LIST QQ binplus bintimes binneg 0 1)))

;;; RR-RING and CC-RING are 7-tuples carrying the structural norm at slot 7
;;; (NORMED-FIELD layout).  Slots 1..6 share RING's accessor indices, but a
;;; 7-tuple does NOT satisfy the length-6 predicates IS-RING / IS-COMMUTATIVE-
;;; RING / IS-INTEGRAL-DOMAIN (each pins length(s)=6).  Asserting those here
;;; was a flat inconsistency (length 6 = length 7); fixed 2026-05-30.  RR/CC
;;; reach the ring world via the NORMED-FIELD-AS-{COMMUTATIVE-RING,INTEGRAL-
;;; DOMAIN} view-as projections (views.scm), which build a fresh 6-tuple from
;;; slots 1..6 -- exactly how FIELD reaches it (FIELD-AS-INTEGRAL-DOMAIN).
(theory-add-axiom! *current-theory* 'rr-ring-def
  '(= RR-RING (LIST RR binplus bintimes binneg 0 1 abs)))

(theory-add-axiom! *current-theory* 'cc-ring-def
  '(= CC-RING (LIST CC binplus bintimes binneg 0 1 magnitude)))

;;; IS-X witnesses, taken as axioms (each true of the domain; no proofs).
;;; CRITICAL: a structure predicate IS-X bakes in length(s)=n, so a tuple can
;;; only witness predicates of its OWN shape.
;;;   ZZ-RING, QQ-RING : 6-tuples -> RING / COMMUTATIVE-RING / INTEGRAL-DOMAIN
;;;                      (and ZZ also EUCLIDEAN-RING; all 6-slot).
;;;   RR-RING, CC-RING : 7-tuples (NORMED-FIELD shape) -> IS-NORMED-FIELD only;
;;;                      ring structure via the NORMED-FIELD-AS-* views.
;;;   QQ as a FIELD     : the separate 8-tuple QQ-FIELD below (FIELD is 8-slot).

(theory-add-axiom! *current-theory* 'zz-is-ring '(IS-RING ZZ-RING))
(theory-add-axiom! *current-theory* 'qq-is-ring '(IS-RING QQ-RING))

(theory-add-axiom! *current-theory* 'zz-is-commutative-ring '(IS-COMMUTATIVE-RING ZZ-RING))
(theory-add-axiom! *current-theory* 'zz-is-integral-domain  '(IS-INTEGRAL-DOMAIN ZZ-RING))
(theory-add-axiom! *current-theory* 'zz-is-euclidean-ring   '(IS-EUCLIDEAN-RING ZZ-RING))

(theory-add-axiom! *current-theory* 'qq-is-commutative-ring '(IS-COMMUTATIVE-RING QQ-RING))
(theory-add-axiom! *current-theory* 'qq-is-integral-domain  '(IS-INTEGRAL-DOMAIN QQ-RING))

(theory-add-axiom! *current-theory* 'rr-is-normed-field     '(IS-NORMED-FIELD RR-RING))
(theory-add-axiom! *current-theory* 'cc-is-normed-field     '(IS-NORMED-FIELD CC-RING))

;;; -----------------------------------------------------------------------
;;; QQ as a field: the 8-tuple QQ-FIELD.
;;;
;;; FIELD is its own 8-slot shape [A ADD MUL NEG ZERO ONE NON-ZERO INV]
;;; (field.scm), so a field instance must be an 8-tuple -- QQ-RING (6) cannot
;;; witness IS-FIELD.  QQ-FIELD carries NON-ZERO = QQ minus {0} (matching
;;; field-non-zero-carrier) and INV = recip; recip's multiplicative-inverse
;;; law (qq-recip-inverse, number-systems.scm) underwrites field-mul-inverse.
(theory-add-axiom! *current-theory* 'qq-field-def
  '(= QQ-FIELD (LIST QQ binplus bintimes binneg 0 1
                     (DIFFERENCE QQ (SINGLETON 0)) recip)))

(theory-add-axiom! *current-theory* 'qq-field-is-field '(IS-FIELD QQ-FIELD))

;;; -----------------------------------------------------------------------
;;; RR-MS -- RR as a metric space, distance |x - y|.
;;;
;;; Mirrors CC-MS (complex.scm).  Completeness is asserted through the
;;; generic IS-COMPLETE predicate (metric-completeness.scm); the bespoke
;;; "rr-complete" the earlier design deferred is exactly IS-COMPLETE(RR-MS).
;;; IS-METRIC-SPACE(RR-MS) is an axiom (provable from the abs axioms in
;;; number-systems.scm once FUN-typing of the lambda is in place).

(def-constant 'RR-MS
  (list 'rr-ms-def
        '(= RR-MS (LIST RR (VNB-LAMBDA (LIST x y) (abs (- x y)))))))

(theory-add-axiom! *current-theory* 'rr-ms-def
  '(= RR-MS (LIST RR (VNB-LAMBDA (LIST x y) (abs (- x y))))))

(theory-add-axiom! *current-theory* 'rr-is-metric-space
  '(IS-METRIC-SPACE RR-MS))

(theory-add-axiom! *current-theory* 'rr-complete
  '(IS-COMPLETE RR-MS))

;;; -----------------------------------------------------------------------
;;; NN as a commutative monoid under addition
;;;
;;; NN-ADD-MONOID = [NN, binplus, 0]
;;;
;;; NN is not a ring (no negation), but it is a commutative monoid under
;;; +, with identity 0.  IS-COMM-MONOID is taken as axiom by the same
;;; rationale as the ring instances above.

(theory-add-axiom! *current-theory* 'nn-add-monoid-def
  '(= NN-ADD-MONOID (LIST NN binplus 0)))

(theory-add-axiom! *current-theory* 'nn-add-monoid-is-comm-monoid
  '(IS-COMM-MONOID NN-ADD-MONOID))

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
(register-definitional-structure! 'RR-RING        'NORMED-FIELD)
(register-definitional-structure! 'CC-RING        'NORMED-FIELD)
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
      (= (+ x y) (REDUCE binplus (FAM-OF-LIST (LIST x y)) 2)))))

(theory-add-axiom! *current-theory* 'nary-plus-3-list
  '(FORALL x (FORALL y (FORALL z
      (= (+ x y z) (REDUCE binplus (FAM-OF-LIST (LIST x y z)) 3))))))

(theory-add-axiom! *current-theory* 'nary-plus-4-list
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (= (+ w x y z) (REDUCE binplus (FAM-OF-LIST (LIST w x y z)) 4)))))))

(theory-add-axiom! *current-theory* 'nary-plus-5-list
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (= (+ v w x y z)
         (REDUCE binplus (FAM-OF-LIST (LIST v w x y z)) 5))))))))

(theory-add-axiom! *current-theory* 'nary-times-2-list
  '(FORALL x (FORALL y
      (= (* x y) (REDUCE bintimes (FAM-OF-LIST (LIST x y)) 2)))))

(theory-add-axiom! *current-theory* 'nary-times-3-list
  '(FORALL x (FORALL y (FORALL z
      (= (* x y z) (REDUCE bintimes (FAM-OF-LIST (LIST x y z)) 3))))))

(theory-add-axiom! *current-theory* 'nary-times-4-list
  '(FORALL w (FORALL x (FORALL y (FORALL z
      (= (* w x y z) (REDUCE bintimes (FAM-OF-LIST (LIST w x y z)) 4)))))))

(theory-add-axiom! *current-theory* 'nary-times-5-list
  '(FORALL v (FORALL w (FORALL x (FORALL y (FORALL z
      (= (* v w x y z)
         (REDUCE bintimes (FAM-OF-LIST (LIST v w x y z)) 5))))))))
