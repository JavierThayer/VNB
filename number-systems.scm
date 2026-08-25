;;; number-systems.scm -- number system constants and axioms
;;;
;;; NN : natural numbers (0, 1, 2, ...)
;;; ZZ : integers
;;; QQ : rationals
;;; RR : reals
;;; CC : complex numbers
;;;
;;; Inclusion chain: NN ⊆ ZZ ⊆ QQ ⊆ RR ⊆ CC
;;;
;;; Single arithmetic operators across all systems:
;;;   +  *  -  recip  abs  conjugate  succ  <=
;;; Numeric literals 0, 1, 2, ... and -1, -2, ... are constants in ZZ
;;; (non-negative literals also in NN via nn-subset-zz and closure axioms)

;;; -----------------------------------------------------------------------
;;; Sethood

(theory-add-axiom! *current-theory* 'nn-is-set      '(IN NN SET))
(theory-add-axiom! *current-theory* 'zz-is-set      '(IN ZZ SET))
(theory-add-axiom! *current-theory* 'qq-is-set      '(IN QQ SET))
(theory-add-axiom! *current-theory* 'rr-is-set      '(IN RR SET))
(theory-add-axiom! *current-theory* 'cc-is-set      '(IN CC SET))

;;; -----------------------------------------------------------------------
;;; Inclusion chain

(theory-add-axiom! *current-theory* 'nn-subset-zz
  '(FORALL n (IMPLIES (IN n NN) (IN n ZZ))))

(theory-add-axiom! *current-theory* 'zz-subset-qq
  '(FORALL n (IMPLIES (IN n ZZ) (IN n QQ))))

(theory-add-axiom! *current-theory* 'qq-subset-rr
  '(FORALL n (IMPLIES (IN n QQ) (IN n RR))))

(theory-add-axiom! *current-theory* 'rr-subset-cc
  '(FORALL n (IMPLIES (IN n RR) (IN n CC))))

;;; -----------------------------------------------------------------------
;;; BINARY MINUS (added 2026-08-01).
;;;
;;; THE GAP THIS CLOSES.  Every minus axiom below is UNARY -- zz/qq/rr/cc-neg-
;;; closed and -neg-inverse all speak of `(- a)'.  The BINARY `(- a b)' that the
;;; parser emits (parser.scm:9, "x - y") had no axiom anywhere: nothing said it
;;; was subtraction, nothing said RR was closed under it.  The only statement in
;;; the tree about it was `rr-sub-in-rr' (order-lemmas.scm), a `well-known'
;;; support asserting closure -- which read like a triviality restating
;;; rr-add-closed and was in fact the sole constraint on an uninterpreted head.
;;;
;;; WHY IT MATTERS beyond tidiness: `ineq' -- the Fourier-Motzkin/Farkas oracle,
;;; a TRUSTED closer -- "linearizes over + - *" by its own documentation, so it
;;; reads `(- a b)' as subtraction when discharging a goal.  Without this axiom
;;; the oracle assumed a meaning the theory declined to state; every Farkas
;;; certificate over a difference (all five in the rr-complete proof) rested on
;;; it.  The conclusion was never in doubt -- the gap was in the licence.
;;;
;;; `==', not `=': quasi-equality is unconditional, so the equation needs no
;;; definedness witness and carries no (IN a RR) guard, exactly as rr-ms-dist
;;; is stated.  Unguarded in a and b for the same reason app-graph is unguarded
;;; (theory.scm): it defines a SYMBOL, and an axiom is instantiated only at
;;; terms.
;;;
;;; DEFINITIONAL, not primitive: this file now loads with *current-provenance*
;;; = 'primitive (load.scm's *primitive-files*), and this fluid-let overrides
;;; that for this one form.  The distinction is the honest one -- the ordered-
;;; field axioms are foundational commitments, whereas this says what a symbol
;;; ABBREVIATES.  Either stamp contributes {} to a bill, so no proof's debt
;;; changes; the catalog counts it as a definition rather than an axiom.
;;;
;;; NAMED-ONLY: as a live macete its left side `(- a b)' matches every binary
;;; difference in every goal and rewrites it to `a + (- b)', un-normalising
;;; arithmetic wherever the rewrite index is consulted automatically (grind,
;;; scout, simp).  That is the app-graph situation exactly: sound, and ruinous
;;; to fire unasked.  Cite it by name when you want it.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'binary-minus-def
    '(FORALL a (FORALL b (== (- a b) (+ a (- b))))))
  (declare-named-only! 'binary-minus-def
    "left side matches every binary difference; firing automatically rewrites
     all arithmetic into additive-inverse form"))

;;; BINARY DIVISION (added 2026-08-02) -- the same disease, one operator over.
;;;
;;; parser.scm:278-293 desugars the infix "x / y" to (* x (recip y)), so surface
;;; input never produces a `/' head.  But a wff written as a QUOTED s-expression
;;; in Scheme source bypasses the parser, and several supports do exactly that:
;;; bdd-fn-nonneg / -lt-one / -le-arg (scalar-inequalities.scm:82,89,96), the
;;; product-metric weights (product-metric.scm:61,145) and young-inequality
;;; (real-powers.scm:180) all contain a literal `(/ a b)'.  Until now no axiom
;;; and no arith-eval rule mentioned that head, so those statements were about
;;; an uninterpreted binary operator: not unsound, but inert -- no proof could
;;; connect them to `recip', which is what the theory actually axiomatises
;;; (rr-recip-closed, rr-recip-inverse) and what arith-eval evaluates.
;;;
;;; Same four choices as binary-minus-def, for the same reasons: `==' so no
;;; definedness witness is owed; unguarded because it defines a SYMBOL; stamped
;;; `definitional' (overriding this file's `primitive' default) because it says
;;; what a symbol abbreviates; and named-only, since as a live macete its left
;;; side matches every quotient in the library.
;;;
;;; NOTE what this does NOT do: it does not make those six supports correct
;;; about division by zero.  (/ a 0) unfolds to (* a (recip 0)), and recip 0 is
;;; undefined -- which is the honest reading, and the reason `=' would have been
;;; the wrong connective here.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'binary-divide-def
    '(FORALL a (FORALL b (== (/ a b) (* a (recip b))))))
  (declare-named-only! 'binary-divide-def
    "left side matches every quotient; firing automatically rewrites all
     arithmetic into recip form"))

;;; -----------------------------------------------------------------------
;;; NN — natural numbers (0, 1, 2, ...)

(theory-add-axiom! *current-theory* 'nn-zero-in '(IN 0 NN))

(theory-add-axiom! *current-theory* 'nn-succ-closed
  '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))))

(theory-add-axiom! *current-theory* 'nn-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (IN (+ a b) NN)))))

(theory-add-axiom! *current-theory* 'nn-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (IN (* a b) NN)))))

(theory-add-axiom! *current-theory* 'nn-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'nn-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'nn-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'nn-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'nn-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'nn-one-mul
  '(FORALL a (IMPLIES (IN a NN) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'nn-add-zero
  '(FORALL a (IMPLIES (IN a NN) (= (+ a 0) a))))

;;; NN induction schema (class form).
;;; For any class C: if 0 ∈ C and (∀n∈NN. n∈C → succ(n)∈C) then ∀n∈NN. n∈C.
;;; Follows from transfinite-induction (ordinals.scm) + NN ⊆ ORD + 0 ∈ NN
;;; + nn-succ-closed; stated here as a named axiom for direct use.
(theory-add-axiom! *current-theory* 'nn-induction
  '(FORALL C
      (IMPLIES (AND (IN 0 C)
                    (FORALL n (IMPLIES (AND (IN n NN) (IN n C))
                                       (IN (succ n) C))))
               (FORALL n (IMPLIES (IN n NN) (IN n C))))))

;;; -----------------------------------------------------------------------
;;; ZZ — integers (ring)

(theory-add-axiom! *current-theory* 'zz-zero-in '(IN 0 ZZ))
(theory-add-axiom! *current-theory* 'zz-one-in  '(IN 1 ZZ))

(theory-add-axiom! *current-theory* 'zz-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (IN (+ a b) ZZ)))))

(theory-add-axiom! *current-theory* 'zz-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (IN (* a b) ZZ)))))

(theory-add-axiom! *current-theory* 'zz-neg-closed
  '(FORALL a (IMPLIES (IN a ZZ) (IN (- a) ZZ))))

(theory-add-axiom! *current-theory* 'zz-add-zero
  '(FORALL a (IMPLIES (IN a ZZ) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'zz-neg-inverse
  '(FORALL a (IMPLIES (IN a ZZ) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'zz-one-mul
  '(FORALL a (IMPLIES (IN a ZZ) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'zz-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'zz-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'zz-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'zz-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'zz-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

;;; GENERATION: every integer is a natural or the negative of one.  Moved here
;;; from structure-library/zz-arith.scm on 2026-08-01, where it was a PSS
;;; support -- it belongs with the axioms that say what ZZ IS, not in a
;;; downstream lemma file.  Without it the ring axioms above do not pin ZZ down
;;; at all: QQ satisfies every one of them, and in QQ nothing is odd and
;;; 2 * (1/2) = 1, so parity is not merely unproven but refutable in a model.
;;; Consumed by zz-parity-proof.scm (:94, :235) under this same name, so the
;;; move is transparent to its callers.
(theory-add-axiom! *current-theory* 'zz-generated-by-nn
  (forall-guarded 'a '(IN a ZZ)
    (forsome-guarded 'n '(IN n NN)
      '(OR (= a n) (= a (- n))))))
(warrant! 'zz-generated-by-nn 'reference
  "Every integer is a natural number or the negative of one -- the defining
   property of ZZ as the ring generated by NN.  Retire it by constructing ZZ
   from NN (difference pairs), at which point it becomes a theorem.")

;;; -----------------------------------------------------------------------
;;; QQ — rationals (ordered field)

(theory-add-axiom! *current-theory* 'qq-zero-in '(IN 0 QQ))
(theory-add-axiom! *current-theory* 'qq-one-in  '(IN 1 QQ))

(theory-add-axiom! *current-theory* 'qq-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (IN (+ a b) QQ)))))

(theory-add-axiom! *current-theory* 'qq-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (IN (* a b) QQ)))))

(theory-add-axiom! *current-theory* 'qq-neg-closed
  '(FORALL a (IMPLIES (IN a QQ) (IN (- a) QQ))))

(theory-add-axiom! *current-theory* 'qq-add-zero
  '(FORALL a (IMPLIES (IN a QQ) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'qq-neg-inverse
  '(FORALL a (IMPLIES (IN a QQ) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'qq-one-mul
  '(FORALL a (IMPLIES (IN a QQ) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'qq-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'qq-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'qq-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'qq-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'qq-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'qq-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a QQ) (NOT (= a 0)))
               (IN (recip a) QQ))))

(theory-add-axiom! *current-theory* 'qq-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a QQ) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

;;; GENERATION: every rational is a * recip(b) with a, b integers, b /= 0.
;;; Added 2026-08-01, the QQ analogue of zz-generated-by-nn above.  Without it
;;; the field axioms do not pin QQ down: RR satisfies every one of them, so
;;; "q is a fraction" is unavailable and any argument that takes a rational
;;; apart (sqrt(2) irrational, denominators, parity of a numerator) has no
;;; foothold.
;;;
;;; Stated WITH recip, per the user's (d).  The pre-existing
;;; `qq-nonneg-is-fraction' (structure-library/qq-fractions.scm) states the
;;; weaker nonneg-over-NN case multiplicatively (q * b = a) precisely to dodge
;;; recip's non-zero side condition; that dodge is not needed here because b /= 0
;;; is a hypothesis of the existential, so recip b is defined wherever the
;;; witness is.  The two are kept both installed for now: deriving the nonneg
;;; form from this one needs a sign split and a ZZ -> NN bridge the library does
;;; not have (see the note in qq-fractions.scm).
(theory-add-axiom! *current-theory* 'qq-is-fraction
  (forall-guarded 'q '(IN q QQ)
    (forsome-guarded 'a '(IN a ZZ)
      (forsome-guarded 'b '(IN b ZZ)
        (conjuncts->and
          (list '(NOT (= b 0))
                '(= q (* a (recip b)))))))))
(warrant! 'qq-is-fraction 'reference
  "Every rational is a quotient of integers -- the defining property of QQ as
   the fraction field of ZZ.  Retire it by constructing QQ as a localization of
   ZZ, at which point it becomes a theorem.")

;;; -----------------------------------------------------------------------
;;; RR — reals (complete ordered field)

(theory-add-axiom! *current-theory* 'rr-zero-in '(IN 0 RR))
(theory-add-axiom! *current-theory* 'rr-one-in  '(IN 1 RR))

(theory-add-axiom! *current-theory* 'rr-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IN (+ a b) RR)))))

(theory-add-axiom! *current-theory* 'rr-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IN (* a b) RR)))))

(theory-add-axiom! *current-theory* 'rr-neg-closed
  '(FORALL a (IMPLIES (IN a RR) (IN (- a) RR))))

(theory-add-axiom! *current-theory* 'rr-add-zero
  '(FORALL a (IMPLIES (IN a RR) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'rr-neg-inverse
  '(FORALL a (IMPLIES (IN a RR) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'rr-one-mul
  '(FORALL a (IMPLIES (IN a RR) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'rr-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'rr-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'rr-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'rr-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'rr-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'rr-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a RR) (NOT (= a 0)))
               (IN (recip a) RR))))

(theory-add-axiom! *current-theory* 'rr-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a RR) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

;;; Order: <= is the numeric order on the real chain (NN/ZZ/QQ/RR/RR-STAR).
;;; A total order compatible with the field operations.  Stated guarded by
;;; (IN _ RR); because the inclusions NN<=ZZ<=QQ<=RR are genuine set
;;; inclusions, these axioms also govern <= on the integers and rationals.
;;; The ordinal order is a separate relation ORD-LE (ordinals.scm), bridged
;;; to <= on NN, so nothing here leaks onto it; CC carries no <=.

(theory-add-axiom! *current-theory* 'rr-leq-reflexive
  '(FORALL a (IMPLIES (IN a RR) (<= a a))))

(theory-add-axiom! *current-theory* 'rr-leq-antisymmetric
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IMPLIES (AND (<= a b) (<= b a)) (= a b))))))

(theory-add-axiom! *current-theory* 'rr-leq-transitive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (IMPLIES (AND (<= a b) (<= b c)) (<= a c)))))))

(theory-add-axiom! *current-theory* 'rr-leq-total
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (OR (<= a b) (<= b a))))))

(theory-add-axiom! *current-theory* 'rr-leq-add-compat
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (IMPLIES (<= a b) (<= (+ a c) (+ b c))))))))

(theory-add-axiom! *current-theory* 'rr-leq-mul-nonneg
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IMPLIES (AND (<= 0 a) (<= 0 b)) (<= 0 (* a b)))))))

;;; -----------------------------------------------------------------------
;;; ABSOLUTE VALUE, DEFINED.  Added 2026-08-17.
;;;
;;; WHY THIS IS A DEFINITION AND NOT DEBT.  Until now `abs' was characterised by
;;; five NORM-shaped axioms -- closed, nonneg, zero-iff, triangle, multiplicative
;;; -- and not one of them related |x| to x.  They do not determine abs: the map
;;; x |-> sqrt(|x|) satisfies all five (nonneg, vanishing only at 0,
;;; multiplicative, subadditive), so |2| = sqrt 2 was a model of the theory as
;;; stated.  Everything that pins |x| to one of x, -x -- x <= |x|, the two-sided
;;; bound |x| <= c iff -c <= x <= c, the reverse triangle inequality -- was
;;; therefore INDEPENDENT of the axioms, not merely unproved, and each had to be
;;; asserted as a `well-known' support in structure-library/order-lemmas.scm.
;;;
;;; The equation below is the textbook definition by cases: on a TOTAL order the
;;; two guards are exhaustive and exclusive, so it defines a unique function on
;;; RR and introduces no assumption.  That is what `primitive' provenance means
;;; here (number-systems.scm is in load.scm's `*primitive-files*'): not "we are
;;; assuming this", but "this is what the symbol MEANS".  Its consequences are
;;; theorems and are proved in theorem-library/rr-abs-basics.scm -- including
;;; the five norm axioms this replaced, which are DELETED from this file.
;;;
;;; THE GUARD IS `NOT (<= 0 x)', NOT `x < 0', deliberately: `<' is defined in
;;; structure-library/order-predicates.scm, which loads AFTER this file, so the
;;; head does not exist yet.  With rr-leq-total the two forms are equivalent,
;;; and rr-abs-basics.scm proves the `<' form as its first theorem.
;;;
;;; CONJUNCTION OF GUARDED EQUATIONS, not an `IF' term: nothing downstream then
;;; needs IF-reduction rules.  `fact' lands the conjunction, `ai' splits it and
;;; `detach!' takes whichever branch the sign hypothesis licenses.
;;; `definitional' rather than this file's `primitive' default, exactly as
;;; binary-minus-def and binary-divide-def above: it says what a SYMBOL means,
;;; not what the reals are.  Both stamps contribute {} to every bill; the
;;; catalog counts this one as a definition rather than an axiom.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'rr-abs-def
    '(FORALL x (IMPLIES (IN x RR)
        (AND (IMPLIES (<= 0 x) (= (abs x) x))
             (IMPLIES (NOT (<= 0 x)) (= (abs x) (- x))))))))

;;; -----------------------------------------------------------------------
;;; MAX on RR -- the binary maximum, DEFINED by cases, 2026-08-19.
;;;
;;; Stated as a DEFINITION and not as a family of properties, for the reason the
;;; note below `rr-abs-def' gives about the five norm-shaped axioms that used to
;;; stand here: "They were not wrong; they were incomplete, and stating them
;;; INSTEAD of the definition is what left x <= |x| independent of the theory."
;;; So `x <= max(x,y)', `max(x,y) in RR' and the rest are NOT axioms; they are
;;; proven from this one equation in theorem-library/rr-max-basics.scm.
;;;
;;; The library's other habit for a maximum is to state it EXISTENTIALLY, as
;;; `rr-min-pos' does for a minimum -- "a positive lower bound of two positives"
;;; rather than a MIN term -- precisely so as not to introduce an operator.
;;; That is right when all a proof needs is the bounding property; it is the
;;; wrong shape when the maximum is a TERM the statement is about, as in the
;;; ultrametric-style inequality d(a,c) <= 2*max(d(a,b), d(b,c)), where the two
;;; occurrences must denote the same thing.  Hence a real operator here.
;;;
;;; `definitional', not this file's `primitive' default, exactly as
;;; rr-abs-def / binary-minus-def / binary-divide-def above: it says what a
;;; SYMBOL means, not what the reals are.
;;;
;;; The guard `(<= y x)' rather than `(< y x)': at x = y both branches give the
;;; same value, so the cases may overlap and the definition is still a function.
;;; Splitting on `<=' means the FIRST branch covers equality, which is what a
;;; proof by cases on `rr-le-total' hands you.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'rr-max-def
    '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
        (AND (IMPLIES (<= y x) (= (max x y) x))
             (IMPLIES (NOT (<= y x)) (= (max x y) y)))))))))

;;; MIN, 2026-08-21, by the same recipe and for the same reason.  One equation
;;; here; every usable fact about it is PROVEN in
;;; theorem-library/rr-min-basics.scm.
;;;
;;; The guard is `(<= x y)' -- the mirror of MAX's `(<= y x)' -- so that here
;;; too the FIRST branch covers equality and returns the FIRST argument, and a
;;; proof by cases on `rr-le-total' meets the branches in the same order for
;;; both operators.  With `(< x y)' the two definitions would disagree at x = y
;;; about which argument they return, which matters not at all to the value and
;;; a great deal to a driver that handles them side by side.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'rr-min-def
    '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
        (AND (IMPLIES (<= x y) (= (min x y) x))
             (IMPLIES (NOT (<= x y)) (= (min x y) y)))))))))

;;; THE FIVE NORM-SHAPED AXIOMS THAT STOOD HERE ARE GONE (2026-08-17):
;;; rr-abs-closed, rr-abs-nonneg, rr-abs-zero, rr-abs-triangle and rr-abs-mult
;;; -- the last of which carried the comment "the conjunct that `is-norm' (hence
;;; `rr-is-normed-field') needs for NRM = abs on RR-NORMED-FIELD".  All five are
;;; PROVEN `modulo 0' from rr-abs-def in theorem-library/rr-abs-basics.scm, with
;;; the same names and the same statements, so every citation still resolves.
;;; They were not wrong; they were incomplete, and stating them INSTEAD of the
;;; definition is what left x <= |x| independent of the theory.

;;; -----------------------------------------------------------------------
;;; ORDER COMPLETENESS of RR -- every inhabited set of reals with an upper
;;; bound has a LEAST one.  Added 2026-08-01.
;;;
;;; This is what makes RR the reals rather than an arbitrary ordered field.
;;; Until now the section header above said "complete ordered field" and the
;;; file delivered an ordered field: the axioms from rr-zero-in to rr-abs-mult
;;; are satisfied by, e.g., the field of rational functions ordered at infinity,
;;; in which the naturals ARE bounded.  Every eps-argument in the analysis layer
;;; bottoms out on the archimedean property, which was therefore not derivable
;;; and had to be asserted (order-predicates.scm).  With these three axioms it
;;; is a theorem; see the note there.
;;;
;;; SHAPE.  Modelled on ESUP for RR-POS-STAR (structure-library/extended-reals-pos.scm:
;;; esup-in / esup-upper / esup-least), which is the one place in the tree that
;;; already states an order-completeness: an `in', an `upper' and a `least'
;;; axiom pinning a supremum operator.  Uniqueness needs no axiom -- upper +
;;; least + antisymmetry of <= pin SUP(S) between any two candidate lubs.
;;;
;;; The difference from ESUP is the GUARD.  POS-INF tops RR-POS-STAR, so there every
;;; subset has a sup and the axioms are unguarded; RR has no top, so the two
;;; hypotheses that a sup needs -- S is inhabited, S is bounded above -- are
;;; hypotheses here.  SUP(S) is left unconstrained outside them (a total symbol
;;; with no stated value, exactly as ESUP is outside RR-POS-STAR), NOT undefined: no
;;; definedness claim is made either way, so nothing can be proved about
;;; SUP(EMPTY-SET).
;;;
;;; `<' and `POS-RR' do not exist yet at this point in the load
;;; (structure-library/order-predicates.scm is load.scm:124, this file is :110),
;;; which is why the QQ-dense-in-RR axiom -- item (c) of the same cleanup, and
;;; naturally stated with strict inequalities -- is sited THERE rather than
;;; here.  It is listed in the manifest comment at the head of this file.

;;; b is an upper bound of S in RR.  (Note it is NOT required that S be a set of
;;; reals -- the axioms below carry that hypothesis separately, so this predicate
;;; stays usable on any class.)
(def-predicate 'RR-UPPER-BOUND '(S b)
  '(AND (IN b RR)
        (FORALL x (IMPLIES (IN x S) (<= x b)))))

;;; S has some upper bound in RR.
(def-predicate 'RR-BOUNDED-ABOVE '(S)
  '(FORSOME b (RR-UPPER-BOUND S b)))

(theory-add-axiom! *current-theory* 'rr-sup-in
  (forall-guarded '(S)
    (list '(SUBSET S RR) '(FORSOME x (IN x S)) '(RR-BOUNDED-ABOVE S))
    '(IN (SUP S) RR)))

(theory-add-axiom! *current-theory* 'rr-sup-upper
  (forall-guarded '(S)
    (list '(SUBSET S RR) '(FORSOME x (IN x S)) '(RR-BOUNDED-ABOVE S))
    '(RR-UPPER-BOUND S (SUP S))))

(theory-add-axiom! *current-theory* 'rr-sup-least
  (forall-guarded '(S)
    (list '(SUBSET S RR) '(FORSOME x (IN x S)) '(RR-BOUNDED-ABOVE S))
    (forall-guarded 'b '(RR-UPPER-BOUND S b)
      '(<= (SUP S) b))))

;;; Notation.  These three calls are not decoration -- two suite gates require
;;; them, and both caught this block on its first run (751/3 instead of 753/1):
;;;   * `unknown-head-audit' (audit.scm:306) holds that every symbol APPLIED in
;;;     an installed theorem is a kernel head, a registered operator, or bound in
;;;     the formula.  SUP is introduced the way ESUP is -- pinned by axioms, with
;;;     no def-functoid -- so nothing registered it and all three axioms were
;;;     flagged.  `notation!' registers the operator as a side effect
;;;     (operators.scm:92-95 creates the entry when it is missing), which is the
;;;     remedy the audit's own comment prescribes.
;;;   * "every predicate in the library has an English reading" holds that a
;;;     def-predicate carries a `notation!' beside its definition; a structure
;;;     gets its noun derived, a predicate cannot.
(notation! 'SUP              'kind 'functoid  'arity 1
           'english "the least upper bound of $1")
(notation! 'RR-UPPER-BOUND   'kind 'predicate 'arity 2
           'english "$2 is an upper bound of $1")
(notation! 'RR-BOUNDED-ABOVE 'kind 'predicate 'arity 1
           'english "$1 is bounded above")

(warrant! 'rr-sup-in 'reference
  "Order completeness of RR: an inhabited set of reals with an upper bound has a
   least upper bound, and SUP names it.  The defining property of the reals.")
(warrant! 'rr-sup-upper 'reference
  "SUP(S) is an upper bound of S.  Half of order completeness.")
(warrant! 'rr-sup-least 'reference
  "SUP(S) is below every upper bound of S.  The other half of order completeness.")

;;; -----------------------------------------------------------------------
;;; CC — complex numbers (field)

(theory-add-axiom! *current-theory* 'cc-zero-in '(IN 0 CC))
(theory-add-axiom! *current-theory* 'cc-one-in  '(IN 1 CC))

(theory-add-axiom! *current-theory* 'cc-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (IN (+ a b) CC)))))

(theory-add-axiom! *current-theory* 'cc-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (IN (* a b) CC)))))

(theory-add-axiom! *current-theory* 'cc-neg-closed
  '(FORALL a (IMPLIES (IN a CC) (IN (- a) CC))))

(theory-add-axiom! *current-theory* 'cc-add-zero
  '(FORALL a (IMPLIES (IN a CC) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'cc-neg-inverse
  '(FORALL a (IMPLIES (IN a CC) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'cc-one-mul
  '(FORALL a (IMPLIES (IN a CC) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'cc-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'cc-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'cc-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'cc-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'cc-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'cc-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a CC) (NOT (= a 0)))
               (IN (recip a) CC))))

(theory-add-axiom! *current-theory* 'cc-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a CC) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

(theory-add-axiom! *current-theory* 'cc-conjugate-closed
  '(FORALL a (IMPLIES (IN a CC) (IN (conjugate a) CC))))

(theory-add-axiom! *current-theory* 'cc-conjugate-involution
  '(FORALL a (IMPLIES (IN a CC) (= (conjugate (conjugate a)) a))))

(theory-add-axiom! *current-theory* 'cc-conjugate-add
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (conjugate (+ a b))
                  (+ (conjugate a) (conjugate b)))))))

(theory-add-axiom! *current-theory* 'cc-conjugate-mul
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (conjugate (* a b))
                  (* (conjugate a) (conjugate b)))))))

(theory-add-axiom! *current-theory* 'cc-self-conj-real
  '(FORALL a (IMPLIES (IN a CC) (IN (* a (conjugate a)) RR))))

;; The product a * conjugate(a) is real (cc-self-conj-real); the inequality
;; lives in RR, where <= is the standard real order.
(theory-add-axiom! *current-theory* 'cc-self-conj-nonneg
  '(FORALL a (IMPLIES (IN a CC)
                      (AND (IN (* a (conjugate a)) RR)
                           (<= 0 (* a (conjugate a)))))))

;;; -----------------------------------------------------------------------
;;; THE IMAGINARY UNIT, and CC as RR adjoin i.  Added 2026-08-01.
;;;
;;; The field axioms above, plus conjugation, do not say what CC is: any field
;;; with an involutive automorphism satisfies them, and nothing forces a square
;;; root of -1 to exist or forces every complex to be x + y i.  These four
;;; axioms do both, and they pin `conjugate' at the same time -- until now it
;;; was an unconstrained involution (cc-conjugate-involution/add/mul say it is a
;;; ring automorphism of order dividing 2; the identity satisfies all three).
;;;
;;; THE CONSTANT IS A READER CONSTANT, not a new symbol.  What is written below
;;; as `+i' is the exact Scheme complex number, so `(* +i +i)' is literally -1
;;; to arith-eval (arith-eval.scm:33-48), not a symbol awaiting a rule.  The VNB
;;; surface spells it `%i' and parser.scm:163 reads that to this same number.
;;; This is item (f) of the same cleanup in miniature: the constants of CC are
;;; whatever exact numbers the reader produces, and arith-eval.scm:125-138
;;; already assigns each literal its home in the chain (exact nonneg integer ->
;;; NN, exact integer -> ZZ, exact real -> QQ and RR, anything exact -> CC).
;;; Writing the axiom over the literal rather than over a fresh constant is what
;;; keeps those two accounts from drifting apart.

(theory-add-axiom! *current-theory* 'cc-i-in '(IN +i CC))

(theory-add-axiom! *current-theory* 'cc-i-squared '(= (* +i +i) -1))

;;; Every complex number is x + y*i with x, y real.  This is the axiom that
;;; makes CC two-dimensional over RR; without it CC could be RR itself.
(theory-add-axiom! *current-theory* 'cc-generated-by-rr
  (forall-guarded 'z '(IN z CC)
    (forsome-guarded 'x '(IN x RR)
      (forsome-guarded 'y '(IN y RR)
        '(= z (+ x (* y +i)))))))

;;; Conjugation fixes the reals and flips i.  With cc-conjugate-add/mul these
;;; two determine conjugate on all of CC (conjugate(x + y i) = x - y i), so the
;;; involution axiom becomes a consequence rather than an independent stipulation.
(theory-add-axiom! *current-theory* 'cc-conjugate-fixes-rr
  (forall-guarded 'a '(IN a RR)
    '(= (conjugate a) a)))

(theory-add-axiom! *current-theory* 'cc-conjugate-i
  '(= (conjugate +i) (- +i)))

(warrant! 'cc-i-in 'reference
  "The imaginary unit is a complex number.  Definitional.")
(warrant! 'cc-i-squared 'reference
  "i*i = -1.  The defining property of the imaginary unit.")
(warrant! 'cc-generated-by-rr 'reference
  "Every complex number is x + y*i with x and y real -- the defining property of
   CC as RR adjoin a square root of -1.  Retire it by constructing CC as
   RR x RR with the twisted product, at which point it becomes a theorem.")
(warrant! 'cc-conjugate-fixes-rr 'reference
  "Conjugation fixes every real.  Definitional for complex conjugation.")
(warrant! 'cc-conjugate-i 'reference
  "Conjugation sends i to -i.  Definitional for complex conjugation.")

;;; -----------------------------------------------------------------------
;;; REAL AND IMAGINARY PART, DEFINED FROM CONJUGATION.  Added 2026-08-17.
;;;
;;; `real-part' and `imag-part' were REGISTERED HEADS WITH NO AXIOM AT ALL:
;;; wff.scm:366 lists them among the term-form heads, interactive.scm:1690
;;; advertises them as "CC -> RR", arith-eval.scm:111-118 evaluates them on
;;; ground literals -- and the theory said nothing whatever about them, so a
;;; symbolic `real-part(z)' was an uninterpreted function application.
;;;
;;; No new assumption is needed to fix that, because the CC layer is already
;;; pinned: cc-generated-by-rr says every complex is x + y*i with x, y real, and
;;; cc-conjugate-closed / -involution / -add / -mul / -fixes-rr / -i determine
;;; conjugation on all of it.  Over a field of characteristic 0 containing i,
;;;
;;;     z + conj z = 2x      and      z - conj z = 2yi
;;;
;;; so the two equations below DEFINE the projections; they are theorems of any
;;; model of the axioms above, not stipulations about a new symbol.
;;;
;;; `==', not `=': quasi-equality is unconditional, so the equation owes no
;;; definedness witness and carries no (IN z CC) guard -- the same choice, for
;;; the same reason, as binary-minus-def and binary-divide-def above.  And
;;; `definitional' rather than this file's `primitive' default, for the same
;;; reason as those two: it says what a symbol ABBREVIATES rather than making a
;;; foundational commitment.  Either stamp contributes {} to a bill.
;;;
;;; NOT named-only, unlike those two: the left side is `real-part(z)', a term
;;; nothing else in the library builds by accident, so firing it automatically
;;; is an ordinary definition unfold rather than a rewrite of all arithmetic.
;;;
;;; What follows FROM them -- real-part(z) and imag-part(z) are real, and
;;; z = real-part(z) + i*imag-part(z) -- is proved in
;;; theorem-library/cc-real-imag.scm.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'real-part-def
    '(FORALL z (== (real-part z) (* (+ z (conjugate z)) (recip 2)))))
  (theory-add-axiom! *current-theory* 'imag-part-def
    '(FORALL z (== (imag-part z) (* (- z (conjugate z)) (recip (* 2 +i)))))))

;;; -----------------------------------------------------------------------
;;; magnitude : CC -> RR  (complex modulus)
;;;
;;; THE SEVEN AXIOMS THAT STOOD HERE ARE GONE (2026-08-17): cc-magnitude-closed,
;;; -nonneg, -zero-iff, -neg, -mul, -triangle and rr-magnitude-is-abs.  They were
;;; the `abs' defect one system up -- five norm-shaped facts saying magnitude is
;;; *a* norm and never which one, so nothing tied |z| to z's coordinates.
;;;
;;; magnitude is now DEFINED, in structure-library/complex.scm (which is where
;;; SQRT first exists), and all seven are PROVEN in
;;; theorem-library/cc-magnitude.scm with the same names and statements.  They
;;; bill the SQRT supports of real-powers.scm at trust `well-known' rather than
;;; contributing {} as primitive axioms; the note in complex.scm says why that
;;; is a disclosure rather than a regression.

;;; -----------------------------------------------------------------------
;;; Exponentiation
;;;
;;; power : (CARTESIAN CC NN) -> CC                    (total on NN)
;;; (power x 0)   = 1                                  (n = 0)
;;; (power x n+1) = (* x (power x n))                  (n ∈ NN)
;;; (power x -n)  = (recip (power x n))                (n ∈ NN, x ≠ 0; conditional, not a FUN typing)

;; Total typing on natural number exponents.  Stated as a closure axiom
;; in 2-argument-application form to match the recursion equations below
;; and the user-facing syntax `(power x n)`.  An earlier form
;;   (IN power (FUN (CARTESIAN CC NN) CC))
;; mismatched the application form: it suggested `power` applied to a
;; single CARTESIAN pair, while the system uses `(power x n)` directly.
(theory-add-axiom! *current-theory* 'power-typing-nonneg
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (IN n NN))
               (IN (power x n) CC)))))

(theory-add-axiom! *current-theory* 'power-zero
  '(FORALL x (IMPLIES (IN x CC) (= (power x 0) 1))))

(theory-add-axiom! *current-theory* 'power-succ
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (IN n NN))
               (= (power x (succ n))
                  (* x (power x n)))))))

(theory-add-axiom! *current-theory* 'power-neg
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (AND (IN n NN) (NOT (= x 0))))
               (= (power x (- n))
                  (recip (power x n)))))))
