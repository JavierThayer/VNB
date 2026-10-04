;;; simple-integral.scm -- THE INTEGRAL OF A [0,+inf]-VALUED FUNCTION, DEFINED.
;;; Definitions only; nothing here is asserted and nothing is proved.
;;;
;;; DECISION 4 of the October roadmap (the user, 2026-10-03): the integral is
;;; DEFINED by simple functions, not characterised.  structure-library/integral.scm
;;; (which loads earlier) states the vocabulary -- PTWISE-*, INDICATOR,
;;; PTWISE-LE, IS-MEASURABLE-FN, IS-SIMPLE-FN -- and, until this file, carried
;;; INTEGRAL as a bare registered head (seeded from *wff-term-form-heads* in
;;; wff.scm) pinned by asserted supports.  This file gives the head its
;;; definition under the same NAME and the same ARITY (omega cA mu f), exactly
;;; as CARD went from a registered head to the def-functoid of cardinality.scm on
;;; 2026-09-20 (docs/card-defined-2026-09-20.md), so every statement already
;;; written with INTEGRAL keeps its meaning and its shape.
;;;
;;; SOURCES.  Rudin, Real and Complex Analysis: Def. 1.16 (simple function,
;;; p. 15), Def. 1.23 (the integral, p. 19).  Thayer, Construction of Measures,
;;; Def. 2.1 / Thm. 2.7 (pp. 8-10).  VNB follows RUDIN's simple functions
;;; (finitely many FINITE values), as integral.scm's header explains.
;;;
;;; (1) SIMPLE-INTEGRAL(omega, mu, s) -- Rudin Def. 1.23 for a simple s:
;;;
;;;        SUM_{y in s(omega)}  y * mu({ x in omega : s(x) = y })
;;;
;;;     The sum is a FINSUM in the commutative monoid RR-POS-STAR-ADD-MONOID
;;;     ([0,+inf] under eplus, extended-reals-pos.scm), over the RANGE
;;;     IMAGE(s, omega).  FINSUM rather than ESUM: the range of a simple function
;;;     is finite, the finite sum is what Rudin writes, and every law the proofs
;;;     need (insertion, union, fibered summation, termwise comparison, a real
;;;     scalar factored out) is a FINSUM law; ESUM over a finite domain would be
;;;     the same number by rps-finsum-mono-set (measure-laws.scm) but would add a
;;;     supremum to every step.  The product is etimes, so a value 0 on a set of
;;;     infinite measure contributes 0 (Rudin's convention 0 * inf = 0, p. 19).
;;;     The definition makes sense for ANY s; it is the integral only when s is
;;;     simple (finite range, measurable level sets), which is where the
;;;     theorems of theorem-library/integral-laws.scm use it.
;;;
;;; (2) INTEGRAL(omega, cA, mu, f) -- Rudin Def. 1.23, the notes' definition:
;;;     the least upper bound in [0,+inf] of the simple integrals of the simple
;;;     measurable s with s <= f pointwise.
;;;
;;;        ESUP { SIMPLE-INTEGRAL(omega, mu, s) : IS-SIMPLE-FN(omega, cA, s),
;;;                                               PTWISE-LE(omega, s, f) }
;;;
;;;     written as the ESUP of a SEP over RR-POS-STAR (the shape
;;;     `integral-sup-of-simple' states).  For a simple f the supremum is
;;;     attained at s = f (theorem `integral-simple', integral-laws.scm), which is
;;;     what makes the integral of a simple function its simple integral and
;;;     `integral-sup-of-simple' -- stated with INTEGRAL inside the set -- the
;;;     definition read back.
;;;
;;; THE BINDERS of both bodies (siy_ six_ iny_ ins_) are used by nothing else in
;;; the tree, so a driver's eigenvariables never capture them (CLAUDE.md, "A
;;; set, IOTA or lambda term the DRIVER builds must use binders that nothing
;;; else binds").
;;;
;;; `def-functoid' installs only a rewrite macete; the two unfold EQUATIONS are
;;; proved as theorems (`simple-integral-unfold', `integral-unfold') at the head
;;; of integral-laws.scm, so `mac-h' can name them.
;;;
;;; Dependencies: extended-reals-pos (RR-POS-STAR, ESUP, eplus,
;;; RR-POS-STAR-ADD-MONOID), extended-arith (etimes), finsum (FINSUM),
;;; injection (IMAGE), integral (IS-SIMPLE-FN, PTWISE-LE).  All load before
;;; integral.scm, so this file may sit immediately after it.
;;; ====================================================================

(def-functoid 'SIMPLE-INTEGRAL '(omega mu s)
  '(FINSUM RR-POS-STAR-ADD-MONOID
     (VNB-LAMBDA siy_ (IMAGE s omega)
       (etimes siy_ (mu (SEP six_ omega (= (s six_) siy_)))))
     (IMAGE s omega)))

(notation! 'SIMPLE-INTEGRAL 'kind 'functoid 'arity 3
           'english "the integral of the simple function $3 over $1 with respect to $2")

(def-functoid 'INTEGRAL '(omega cA mu f)
  '(ESUP (SEP iny_ RR-POS-STAR
           (FORSOME ins_
             (AND (IS-SIMPLE-FN omega cA ins_)
                  (AND (PTWISE-LE omega ins_ f)
                       (= iny_ (SIMPLE-INTEGRAL omega mu ins_))))))))

(notation! 'INTEGRAL 'kind 'functoid 'arity 4
           'english "the integral of $4 over $1 with respect to the measure $3")
