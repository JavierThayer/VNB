;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; baire-category.scm -- interior/closure, nowhere-dense, meager/nonmeager, and
;;; the BAIRE CATEGORY theorem (statement only).  Seed for functional analysis.
;;; Added 2026-07-22.  Uses "meager / nonmeager" (per the user: "1st/2nd category
;;; terminology is bad").  Builds on metric-open-sets (IS-OPEN, IS-CLOSED).
;;; ====================================================================

;;; ---- interior / closure of a set --------------------------------------

;;; INTERIOR(s, A): the points with an open neighbourhood contained in A.
(def-functoid 'INTERIOR '(s A)
  '(SEP x (PTS s)
     (FORSOME u (AND (IS-OPEN s u) (AND (IN x u) (SUBSET u A))))))

;;; CLOSURE(s, A): the points every open neighbourhood of which meets A.
(def-functoid 'CLOSURE '(s A)
  '(SEP x (PTS s)
     (FORALL u (IMPLIES (AND (IS-OPEN s u) (IN x u))
       (FORSOME y (AND (IN y u) (IN y A)))))))

;;; ---- category vocabulary ----------------------------------------------

;;; IS-NOWHERE-DENSE(s, A): the closure of A has empty interior.
(def-predicate 'IS-NOWHERE-DENSE '(s A)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(SUBSET A (PTS s))
      '(= (INTERIOR s (CLOSURE s A)) EMPTY-SET))))
(notation! 'IS-NOWHERE-DENSE 'kind 'predicate 'arity 2
           'english "$2 is nowhere dense in $1")

;;; IS-MEAGER(s, A): A is contained in a countable union of nowhere-dense sets
;;; (a countable family ee : NN -> POWER(PTS s), each ee(n) nowhere dense).
(def-predicate 'IS-MEAGER '(s A)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(SUBSET A (PTS s))
      (forsome-guarded 'ee '(IN ee (FUN NN (POWER (PTS s))))
        (conjuncts->and
          (list
            (forall-guarded 'n '(IN n NN) '(IS-NOWHERE-DENSE s (ee n)))
            '(SUBSET A (BIG-UNION n NN (ee n)))))))))
(notation! 'IS-MEAGER 'kind 'predicate 'arity 2
           'english "$2 is meager in $1")

;;; IS-NONMEAGER(s, A): A is not meager.
(def-predicate 'IS-NONMEAGER '(s A)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(SUBSET A (PTS s))
      '(NOT (IS-MEAGER s A)))))
(notation! 'IS-NONMEAGER 'kind 'predicate 'arity 2
           'english "$2 is nonmeager in $1")

;;; ---- the Baire category theorem ---------------------------------------

;;; A complete metric space is nonmeager in itself: it is not a countable union
;;; of nowhere-dense sets.  (Equivalently, a countable intersection of dense open
;;; sets is dense -- the Gdelta form -- see the gloss.)
;;;
;;; THE SPACE MUST BE INHABITED (guard added 2026-09-20, decision of the user).
;;; METRIC-SPACE has no inhabitedness clause, and on PTS(s) = EMPTY-SET the unguarded
;;; statement is FALSE: IS-COMPLETE(s) holds vacuously (FUN(NN, EMPTY-SET) is empty,
;;; so there is no Cauchy sequence), while PTS(s) is meager (the constant family
;;; n |-> EMPTY-SET consists of nowhere-dense sets and covers it).  The guard is a
;;; SEPARATE, curried antecedent, spelled as compact-metric-is-separable spells it,
;;; so that `fact' can detach it.  Found by rake batch 8-C (2026-09-19).
;;; baire-category PROVEN 2026-09-20 (batch 13-C): theorem-library/rake-baire-2.scm (the gloss! and topic! stay here)
(gloss! 'baire-category
  "Baire category theorem: a complete NONEMPTY metric space s is nonmeager in itself -- PTS(s)
   is not contained in any countable union of nowhere-dense sets.  Equivalent Gdelta
   form: a countable intersection of dense open subsets of s is dense.  Proof: nested
   nonempty closed balls of radii -> 0 have a common point (completeness), so no
   countable family of nowhere-dense sets can cover s.  Terminology per the user:
   meager = first category, nonmeager = second category.  Sources: Yosida 0.2; the
   user's notes (exercise).")
(topic! 'baire-category 'topology)
