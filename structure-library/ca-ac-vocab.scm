;;; ca-ac-vocab.scm -- UNIFORM CONVERGENCE ON COMPACT SUBSETS of an open set of CC.
;;; and ZEROS-ACCUMULATE-AT, an accumulation point of the zeros of a function.
;;; DEFINITIONS ONLY; the laws and Proposition 3.44 of complex-analysis.pdf are proven in
;;; theorem-library/weierstrass-convergence.scm, Proposition 2.12 and Corollary 2.13 in
;;; theorem-library/analytic-continuation.scm.  Agent CA-AC, 2026-10-14 (a NEW
;;; DEFINITION, the user's to confirm).
;;;
;;;     UNIF-ON-COMPACTA(u, fam, f)   for every subset K of u that is compact as a metric
;;;                                   space (the subspace of CC-MS on K), the sequence of
;;;                                   functions fam converges to f uniformly on K: for every
;;;                                   eps > 0 there is a threshold N in NN such that
;;;                                   |fam(k)(y) - f(y)| <= eps for every k >= N and every
;;;                                   y in K.
;;;
;;; THE FORM.  "K compact" is IS-COMPACT(SUBSPACE-MS(CC-MS, K)), the form of
;;; `path-trace-compact' and of `heine-borel-ccint'; the uniform clause is, binder for
;;; binder apart from the names, the clause `mrr-unif' of theorem-library/morera.scm
;;; (`holomorphic-uniform-limit' states LOCALLY uniform convergence with it), so the
;;; two notions meet without rewriting.  The bound is `<= eps', as there.  Nothing is
;;; asked of fam(k) or f off K; the typing of the members (fam(k) in FUN(u, CC)) and of
;;; the limit is left to the statements that use the predicate, as `holomorphic-uniform-
;;; limit' does.  The body's binders (wcq_, wce_, wcn_, wck_, wcy_) are used by no other
;;; predicate body; `K' is not spelled `K' (it would fold onto the index `k').
;;;
;;; STATEMENT CHECK.  With u = EMPTY-SET the only K is the empty set and the predicate
;;; holds for every fam and f, which is the standard reading.  The predicate does not
;;; require u to be open; on an open u it is equivalent to LOCALLY uniform convergence
;;; (`unif-on-compacta-locally', `locally-uniform-on-compacta', proven).

(def-predicate 'UNIF-ON-COMPACTA '(u fam f)
  '(FORALL wcq_ (IMPLIES (SUBSET wcq_ u)
     (IMPLIES (IS-COMPACT (SUBSPACE-MS CC-MS wcq_))
       (FORALL wce_ (IMPLIES (POS-RR wce_)
         (FORSOME wcn_ (AND (IN wcn_ NN)
           (FORALL wck_ (IMPLIES (IN wck_ NN) (IMPLIES (<= wcn_ wck_)
             (FORALL wcy_ (IMPLIES (IN wcy_ wcq_)
               (<= (magnitude (- ((fam wck_) wcy_) (f wcy_))) wce_))))))))))))))

(notation! 'UNIF-ON-COMPACTA 'kind 'predicate 'arity 3
           'english "$2 converges to $3 uniformly on the compact subsets of $1")

;;;     ZEROS-ACCUMULATE-AT(u, f, a)  a is an accumulation point of the set of zeros of f
;;;                                   in u: every ball B(a, r), r > 0, of CC-MS contains a
;;;                                   point x of u, distinct from a, with f(x) = 0.
;;;
;;; THE FORM.  The notes (complex-analysis.pdf, before Prop 2.12): "a is an accumulation
;;; point of A if for every neighborhood V of a there is an x in V intersected with A
;;; distinct from a"; the neighbourhoods are taken to be the open balls, which is
;;; equivalent, and A is the zero set {x in u : f(x) = 0}, written out in place so that
;;; no SEP has to be opened.  Whether a itself lies in u is NOT part of the predicate:
;;; the statements that use it say so (the notes ask for an accumulation point IN U).
;;; Binders acr_, acx_ are used by no other predicate body.
(def-predicate 'ZEROS-ACCUMULATE-AT '(u f a)
  '(FORALL acr_ (IMPLIES (POS-RR acr_)
     (FORSOME acx_ (AND (IN acx_ u) (AND (IN acx_ (BALL CC-MS a acr_))
                         (AND (NOT (= acx_ a)) (= (f acx_) 0))))))))

(notation! 'ZEROS-ACCUMULATE-AT 'kind 'predicate 'arity 3
           'english "the zeros of $2 in $1 accumulate at $3")
