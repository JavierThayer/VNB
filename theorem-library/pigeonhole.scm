;;; theorem-library/pigeonhole.scm
;;;
;;; Infinite Pigeonhole, as a Proof Support Set entry.
;;;
;;; Any function from an infinite set to a finite set has an infinite
;;; fiber: some target value is hit by infinitely many domain points.
;;;
;;; Formally: if S is an infinite set, F is a finite set, and
;;; pi : S -> F is a function, then there exists c in F such that
;;; the fiber  SEP x S, pi(x) = c  is itself infinite.
;;;
;;; Workhorse for nested-pigeonhole / diagonalisation arguments.
;;; The totally-bounded => has-Cauchy-subseq theorem uses this at every
;;; recursion step: given infinite S_k subset NN of indices and a finite
;;; cover {c_1, ..., c_n} of PTS(s) by r_k-balls, the function
;;; pi(m) = "which ball center is x_m closest to" gives an infinite
;;; fiber, and that's S_{k+1}.
;;;
;;; Standard proof: contrapositive.  Finite union of finite sets is
;;; finite (NN-induction on the number of pieces using card-union-
;;; disjoint).  Accepted here without mechanical proof during the
;;; library-building phase.

(support 'pigeonhole-infinite
  '(FORALL S
     (IMPLIES (AND (IN S SET) (NOT (IN (CARD S) NN)))
       (FORALL F
         (IMPLIES (AND (IN F SET) (IN (CARD F) NN))
           (FORALL pi
             (IMPLIES (IN pi (FUN S F))
               (FORSOME c
                 (AND (IN c F)
                      (NOT (IN (CARD (SEP x S (= (pi x) c))) NN)))))))))))

(warrant! 'pigeonhole-infinite 'well-known
  "Infinite pigeonhole, standard and asserted here from the argument this file
   already states: contrapositive.  If every fiber SEP x S (pi(x) = c) were
   finite, S would be a finite union of finite sets -- NN-induction on |F| using
   card-union-disjoint -- hence finite, contradicting (NOT (IN (CARD S) NN)).
   Never mechanised: there is NO script for it in
   archive/proven-theorems-archive.scm, despite the promoted-batch wording used
   by its neighbours.  Workhorse of the nested-pigeonhole and diagonalisation
   arguments (totally-bounded => has-Cauchy-subsequence uses it at every
   recursion step), so it is the highest-value target in this batch for an
   actual proof.")
