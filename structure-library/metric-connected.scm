;;; metric-connected.scm -- CONNECTEDNESS OF A SUBSET OF A METRIC SPACE.
;;; DEFINITION ONLY; the laws are PROVEN in theorem-library/metric-connected-laws.scm.
;;; Agent CA-5 of week 3 of the October roadmap, 2026-10-04 (a NEW DEFINITION, the
;;; user's to confirm).
;;;
;;; WHY.  complex-analysis.pdf uses connectedness from chapter 2 on (2.13, the identity
;;; theorem; 3.19, simply connected; 3.27 and 3.30, the winding number on the connected
;;; components of C \ gamma*; 3.55, the maximum modulus principle) and never defines it:
;;; it is the standard notion.  The tree had no connectedness at all (week 1, gap 1;
;;; week 2, gap 3).
;;;
;;;     IS-CONNECTED(s, A)   s is a metric space, A a subset of its points, and no two
;;;                          open sets U, V of s SEPARATE A: whenever A is covered by
;;;                          U union V, no point of A lies in both, and A meets U, then
;;;                          A does not meet V.
;;;
;;; THE FORM.  This is the open-set form ("no two disjoint relatively open nonempty sets
;;; cover A"), written with open sets of the AMBIENT space s: a relatively open subset
;;; of A is A intersected with an open set of s, and "disjoint relatively open" is
;;; "A meets no point of U and V together".  The separation is stated as an
;;; implication ending in "A does not meet V" rather than as the negation of a
;;; four-fold conjunction: the two are propositionally equivalent, and the curried form
;;; is what `fact' detaches (CLAUDE.md: prefer curried antecedents).  The relative
;;; form is chosen over "A is connected as the metric space SUBSPACE-MS(s, A)" because
;;; every use (the winding number, the identity theorem) has A inside an ambient space
;;; and its open sets in hand; the two are equivalent through subspace-open sets, which
;;; the tree does not yet relate to ambient ones.
;;;
;;; STATEMENT CHECKS.  (1) IS-METRIC-SPACE(s) is a conjunct: without it IS-OPEN(s, _)
;;; is never true and every subset would be "connected" vacuously.  (2) The empty set
;;; is connected (the hypothesis "A meets U" fails), as in the usual convention; a
;;; one-point set is connected.  (3) A is required to lie in PTS(s).  (4) No FORSOME
;;; witness or IOTA is formed; the predicate is a plain first-order condition.
;;; (5) BINDERS cns_ cna_ (the parameters), cnu_ cnv_ (the open sets), cnx_ (a point);
;;; no other body or driver in the tree binds a cn?_ name, and none folds onto a class
;;; name, an accessor or a registered constant.
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, PTS), metric-open-sets.scm
;;; (IS-OPEN), the set kernel (SUBSET, UNION).  Load slot: after
;;; structure-library/metric-open-sets.

(def-predicate 'IS-CONNECTED '(cns_ cna_)
  '(AND (IS-METRIC-SPACE cns_)
   (AND (SUBSET cna_ (PTS cns_))
        (FORALL cnu_ (IMPLIES (IS-OPEN cns_ cnu_)
          (FORALL cnv_ (IMPLIES (IS-OPEN cns_ cnv_)
            (IMPLIES (SUBSET cna_ (UNION cnu_ cnv_))
              (IMPLIES (FORALL cnx_ (IMPLIES (IN cnx_ cna_)
                                             (NOT (AND (IN cnx_ cnu_) (IN cnx_ cnv_)))))
                (IMPLIES (FORSOME cnx_ (AND (IN cnx_ cna_) (IN cnx_ cnu_)))
                  (NOT (FORSOME cnx_ (AND (IN cnx_ cna_) (IN cnx_ cnv_))))))))))))))

(notation! 'IS-CONNECTED 'kind 'predicate 'arity 2
           'english "$2 is a connected subset of the metric space $1")
