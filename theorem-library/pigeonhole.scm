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

;;; pigeonhole-infinite RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-combinatorics2.scm

