;;; mb-vocab.scm -- vocabulary for the M-B wave (construction-of-measures.pdf 2.9, 3.2-3.4,
;;; 4.5, 4.13).  DEFINITIONS ONLY.  Agent M-B, 2026-10-26 (new definitions under the rule
;;; "missing vocabulary is not a stopping point").
;;; DESTINATION: structure-library/mb-vocab.scm, after structure-library/outer-measure-construction
;;; (IS-NULL-SET).  Library: measure.
;;;
;;;   IS-CONULL(omega, ca, mu, cs)   the notes before Prop. 2.9: "A set A in A is mu-conull iff
;;;                                  its complement has mu measure 0".
;;;
;;; BINDERS: none (a plain conjunction of the parameters).

(def-predicate 'IS-CONULL '(omega ca mu cs)
  '(AND (IN cs ca) (= (mu (COMPLEMENT-IN omega cs)) 0)))
(notation! 'IS-CONULL 'kind 'predicate 'arity 4
           'english "$4 is a conull set of the measure $3 on $2")

;;;   SYM-DIFFERENCE(a, b)           the notes' A (triangle) B of Prop. 3.2: (A \ B) u (B \ A).
;;;                                  BINDERS: sda_ sdb_ (parameters only).
(def-functoid 'SYM-DIFFERENCE '(sda_ sdb_)
  '(UNION (COMPLEMENT-IN sda_ sdb_) (COMPLEMENT-IN sdb_ sda_)))
(notation! 'SYM-DIFFERENCE 'kind 'functoid 'arity 2
           'english "the symmetric difference of $1 and $2")

;;;   COMPLETION-SIGMA(omega, ca, mu)    the mu-completion of ca (the paragraph before Prop. 3.3):
;;;                                      the subsets of omega of the form A u N, A in ca, N mu-null.
;;;   COMPLETION-MEASURE(omega, ca, mu)  the completion of mu: the method-I outer measure of mu
;;;                                      (Def. 4.8) restricted to the completion.  The notes define
;;;                                      it by mu-bar(A u N) = mu(A); that equation is the THEOREM
;;;                                      completion-measure-value, so the definition needs no IOTA
;;;                                      and no choice of representation.
;;;                                      The null part carries the conjunct `cpn_ in POWER(omega)'
;;;                                      (2026-10-28): NBG separation wants every binder of a SEP
;;;                                      condition confined to sets.  The meaning is unchanged:
;;;                                      A u N in POWER(omega) already forces N to be a subset of omega.
;;; BINDERS: cps_ cpa_ cpn_.
(def-functoid 'COMPLETION-SIGMA '(omega ca mu)
  '(SEP cps_ (POWER omega)
     (FORSOME cpa_ (AND (IN cpa_ ca)
       (FORSOME cpn_ (AND (IN cpn_ (POWER omega)) (AND (IS-NULL-SET omega ca mu cpn_) (= cps_ (UNION cpa_ cpn_)))))))))
(notation! 'COMPLETION-SIGMA 'kind 'functoid 'arity 3
           'english "the completion of the sigma-algebra $2 with respect to $3")

(def-functoid 'COMPLETION-MEASURE '(omega ca mu)
  '(RES (METHOD-I-OUTER omega ca mu) (COMPLETION-SIGMA omega ca mu)))
(notation! 'COMPLETION-MEASURE 'kind 'functoid 'arity 3
           'english "the completion of the measure $3 on $2")
