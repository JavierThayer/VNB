;;; inf-subsets.scm -- the class of infinite subsets of a given set.
;;;
;;; INF-SUBSETS(A) = { S subset A : CARD(S) not in NN }
;;;
;;; "Infinite" means CARD lands in ORD \ NN (an infinite ordinal),
;;; the convention used uniformly with CARD throughout the library.
;;;
;;; Useful as a domain restriction for operators that only make sense
;;; on infinite sets -- e.g. a strictly-monotone enumeration NN -> S
;;; (forthcoming NN-ENUM) is only well-defined for S in INF-SUBSETS(NN).

(def-functoid 'INF-SUBSETS '(A)
  '(SEP S (POWER A) (NOT (IN (CARD S) NN))))

;;; inf-subsets-membership: S in INF-SUBSETS(A) iff S subset A and S infinite.
;;; Follows from SEP membership + POWER membership; recorded as a usable
;;; lemma so proofs can rewrite by name.
(theory-add-axiom! *current-theory* 'inf-subsets-membership
  '(FORALL A
     (FORALL S
       (IFF (IN S (INF-SUBSETS A))
            (AND (SUBSET S A) (NOT (IN (CARD S) NN)))))))

;;; inf-subsets-is-set: INF-SUBSETS(A) in SET when A in SET.
;;; Direct from SEP sethood (POWER A in SET when A in SET).
(theory-add-axiom! *current-theory* 'inf-subsets-is-set
  '(FORALL A
     (IMPLIES (IN A SET)
       (IN (INF-SUBSETS A) SET))))
