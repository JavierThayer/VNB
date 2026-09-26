;;; inf-subsets-is-set.scm -- INF-SUBSETS(A) is a set when A is, proven.
;;;
;;;     forall A.  A in SET  =>  INF-SUBSETS(A) in SET
;;;
;;; INF-SUBSETS(A) is the def-functoid  (SEP S (POWER A) (NOT (IN (CARD S) NN)))
;;; (structure-library/inf-subsets.scm:12), so its sethood is SEP sethood over
;;; the power set, and POWER A is a set by the base axiom `power-set'.  The
;;; axiom of the same name (inf-subsets.scm:26) carries NO warrant, which is
;;; what makes block-family-combinatorial and totally-bounded-has-cauchy-
;;; subsequence the library's two `trust: none' bills.
;;;
;;; PLAN.  (di) (mac 'INF-SUBSETS) (sep-set) leaves (IN (POWER A) SET);
;;; (fact 'power-set 'A) (ass).
;;;
;;; WINDOW.  Cites only the INF-SUBSETS macete (structure-library/inf-subsets)
;;; and `power-set' (library.scm base), so lo = any theorem-library slot after
;;; driver-kit / proof-debt.  hi = theorem-library/block-family-combinatorial-
;;; proof, the only `fact' of it in the tree.
;;;
;;; Helper prefix: iss- (none needed).

(sp (make-wff '(FORALL A (IMPLIES (IN A SET) (IN (INF-SUBSETS A) SET)))))
(di)                      ; lands (IN A SET)
(mac 'INF-SUBSETS)        ; goal: (IN (SEP S (POWER A) ...) SET)
(sep-set)                 ; goal: (IN (POWER A) SET)
(fact 'power-set 'A)
(ass)
(qed 'inf-subsets-is-set)
(topic! 'inf-subsets-is-set 'constructions)
