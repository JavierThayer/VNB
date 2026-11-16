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
;;; RETIRED 2026-09-14 (proven): inf-subsets-is-set -- theorem-library/inf-subsets-is-set.scm
;;; RETIRED 2026-09-14 (proven): nn-in-inf-subsets -- theorem-library/nn-infinite.scm

(def-functoid 'INF-SUBSETS '(A)
  '(SEP S (POWER A) (NOT (IN (CARD S) NN))))

;;; inf-subsets-membership: S in INF-SUBSETS(A) iff S is a set, S subset A and S
;;; infinite.  Follows from SEP membership + POWER membership; recorded as a usable
;;; lemma so proofs can rewrite by name.
;;; THE `S in SET' CONJUNCT (D8, 2026-11-15; DEFSTAMP F2, the user's decision "fix
;;; F1/F2").  Until 2026-11-15 the right side read only `S subset A and not(CARD(S) in
;;; NN)'.  INF-SUBSETS(A) is a SEP over POWER(A), so a member is a SET; without the
;;; conjunct the stamp gave, at A := S := ORD (subset-refl; CARD(ORD) not in NN),
;;; ORD in INF-SUBSETS(ORD), hence ORD in SET, and with Burali-Forti 0 = 1 modulo 0.
(add-axiom! *library* 'inf-subsets-membership
  '(FORALL A
     (FORALL S
       (IFF (IN S (INF-SUBSETS A))
            (AND (IN S SET) (AND (SUBSET S A) (NOT (IN (CARD S) NN))))))))

;;; inf-subsets-is-set: INF-SUBSETS(A) in SET when A in SET.
;;; Direct from SEP sethood (POWER A in SET when A in SET).

;;; nn-in-inf-subsets: NN is an infinite subset of itself.  NN subset NN
;;; (reflexive) and CARD(NN) not in NN (NN is infinite).  The base of the
;;; block-family recursion (blk(0) = NN) and a handy INF-SUBSETS(NN) witness.
