;;; theorem-library/diagonalization.scm
;;;
;;; Diagonalization (classical form), as a Proof Support Set entry.
;;; Matches Remark 3.30 in the analysis notes (calculus.pdf):
;;; given a *nested* family of infinite subsets of NN, extract a single
;;; strictly-monotone sequence whose tail lies inside every member.
;;;
;;; Statement:
;;;
;;;   Given S : NN -> INF-SUBSETS(NN) with S(succ k) subset S(k) for all k,
;;;   there is a strictly monotone f : NN -> NN such that for every k
;;;   and every j >= k, f(j) in S(k).
;;;
;;; The tail-in-S_k property (not just f(k) in S(k)) is the load-bearing
;;; conclusion: it lets compactness arguments conclude that pairs at
;;; indices >= k both lie in S_k, which is what forces the diagonal
;;; sequence to be Cauchy when the S_k are nested r_k-balls with r_k -> 0.
;;;
;;; Note that f(k) in S(k) follows by taking j = k in the conclusion.
;;;
;;; Standard proof: NN-recursion with f(0) := MIN-NN(S(0)) and
;;; f(succ k) := MIN-NN { x in S(succ k) : f(k) < x }; well-foundedness of
;;; NN supplies the minima, infinitude of each S(k) ensures non-emptiness,
;;; and nesting carries f(j) in S(j) up to f(j) in S(k) for k <= j.
;;; Accepted here without mechanical proof during the library-building
;;; phase.

;; Conclusion stated with the factored STRICTLY-MONO-NN predicate (which IS
;; `IN f (FUN NN NN)' AND the spelled-out monotonicity), not the inline form --
;; library hygiene, and it lets the produces-witness index key this lemma under
;; (STRICTLY-MONO-NN ?w), matching a Cauchy-subsequence goal's own witness shape.
(support 'diagonalization
  '(FORALL S
     (IMPLIES (IN S (FUN NN (INF-SUBSETS NN)))
       (IMPLIES (FORALL k
                  (IMPLIES (IN k NN) (SUBSET (S (succ k)) (S k))))
         (FORSOME f
           (AND (STRICTLY-MONO-NN f)
                (FORALL k
                  (IMPLIES (IN k NN)
                    (FORALL j
                      (IMPLIES (IN j NN)
                        (IMPLIES (<= k j) (IN (f j) (S k)))))))))))))
