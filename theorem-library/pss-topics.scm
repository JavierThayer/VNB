;;; pss-topics.scm -- the PSS partition (PSS review, 2026-06-26).
;;;
;;; One (topic! 'name 'cat) per live PSS support, filing it under a bucket
;;; from *pss-topic-order* (macetes.scm).  The category is also the INTAKE
;;; DISCIPLINE: when a proof is blocked and a fact is asserted instead of
;;; ground out, the bucket records WHAT KIND of fact it is and why grinding is
;;; not worth it (see each section title's "why not grind" line in PSS.md).
;;;
;;; Loaded LAST (after every support is installed) so the -rev propagation and
;;; write-pss-md grouping see a complete table.  NEW supports should add their
;;; own (topic! ...) -- inline after the statement (like warrant!) or here;
;;; load.scm soft-nudges any that stay unfiled.
;;;
;;; The eight buckets:
;;;   plumbing      typing / SEP-IMAGE-membership slices / base cases / carrier
;;;                 readouts / ord-segment + set-algebra -- the engine can't
;;;                 unfold these in the needed direction; naming them is cheaper
;;;                 than re-deriving a definition by hand.
;;;   inequalities  order chains, abs, SOS scalar + finite-sum inequalities,
;;;                 root monotonicity, eps-density -- the ineq/sos oracle does
;;;                 not reach it (roots, or it IS the oracle's spec).
;;;   combinatorial pigeonhole / diagonal / block / counting / choice-construction
;;;                 soundness / permutation-reindex / well-ordering -- a genuine
;;;                 but long induction+choice with no library payoff in grinding.
;;;   analysis      limits / series / completeness / summability / monotone
;;;                 convergence / sup-inf -- rests on order-completeness of RR
;;;                 not yet built as named lemmas; assert + cite the book.
;;;   algebra       ring / power / finsum-ring / sum-set / ideal identities and
;;;                 recurrences -- routine structural induction over a monoid /
;;;                 ring / group; the recursion is mechanical, the law reusable.
;;;   topology      open/closed sets, continuity, ball geometry, compactness
;;;                 characterisations -- textbook calculus.pdf; the statement is
;;;                 the interface other proofs cite, the proof is standard.
;;;   constructions metric-space constructions (bounded / product / completion /
;;;                 normed) -- mechanical re-verification of carrier + axioms
;;;                 for a built metric object.
;;;   set-quotient  set & quotient constructions (setoid equivalence, classes,
;;;                 descent, the universal property) -- mechanical verification
;;;                 of a quotient's defining mapping property.

;;; ===== plumbing & typing =====
(topic! 'centres-mem-build 'plumbing)
(topic! 'centres-in-carrier 'plumbing)
(topic! 'centres-ball-eq 'plumbing)
(topic! 'ball-cover-mem-fwd 'plumbing)
(topic! 'centre-set-contains-choice 'plumbing)
(topic! 'open-cover-covers-point 'plumbing)
;; subset-mem-fwd is PROVEN now; it is filed beside its proof in subset-lemmas.scm
(topic! 'ball-point-le 'plumbing)
(topic! 'ball-point-ne 'plumbing)
(topic! 'range-membership 'plumbing)
(topic! 'fun-range-membership 'plumbing)
(topic! 'ran-subset-codomain 'plumbing)
(topic! 'compose-type-2 'plumbing)
(topic! 'compose-type-3 'plumbing)
(topic! 'compose-type-4 'plumbing)
(topic! 'compose-type-5 'plumbing)
(topic! 'compose-apply 'plumbing)
(topic! 'compose-type 'plumbing)
(topic! 'gauges-mem-build 'plumbing)
(topic! 'gauges-in-fun 'plumbing)
(topic! 'gauges-spec 'plumbing)
(topic! 'choose-in-nn 'plumbing)
(topic! 'falling-in-nn 'plumbing)
(topic! 'cauchy-seq-is-fun 'plumbing)
(topic! 'subseq-is-fun 'plumbing)
(topic! 'ball-membership 'plumbing)
(topic! 'ball-is-set 'plumbing)
(topic! 'metric-dist-real 'plumbing)
(topic! 'nag-metric-carrier 'plumbing)
(topic! 'nf-metric-carrier 'plumbing)
(topic! 'bdd-metric-carrier 'plumbing)
(topic! 'product-metric-carrier 'plumbing)
(topic! 'nn-in-rr 'plumbing)
(topic! 'nn-le-refl 'plumbing)
(topic! 'fun-apply-type-c 'plumbing)
(topic! 'ring-power-type 'plumbing)
(topic! 'prod-ring-type 'plumbing)
(topic! 'rpow-pos 'plumbing)
(topic! 'power-real-closed 'plumbing)
(topic! 'nn-minus-in-nn 'plumbing)
(topic! 'ord-segment-insert 'plumbing)
(topic! 'finsum-comm-monoid-type 'plumbing)
(topic! 'finsum-type 'plumbing)
(topic! 'finsum-empty 'plumbing)
(topic! 'finsum-singleton 'plumbing)
(topic! 'prod-ring-empty 'plumbing)
(topic! 'prod-ring-singleton 'plumbing)
(topic! 'card-singleton 'plumbing)
(topic! 'enum-fam-in-fun 'plumbing)
(topic! 'fin-enum-is-bijection 'plumbing)
(topic! 'ord-segment-nn-subset 'plumbing)
(topic! 'ord-segment-nn-succ 'plumbing)
(topic! 'ord-segment-self 'plumbing)
(topic! 'ord-segment-trans 'plumbing)
(topic! 'ord-segment-zero-no-members 'plumbing)
(topic! 'difference-membership 'plumbing)
(topic! 'difference-set 'plumbing)
(topic! 'card-subset-nn 'plumbing)
(topic! 'card-power-nn 'plumbing)
(topic! 'succ-nn-ord 'plumbing)
(topic! 'union-empty-left 'plumbing)
(topic! 'class-subset-carrier 'plumbing)
(topic! 'class-is-set 'plumbing)
(topic! 'quotient-is-set 'plumbing)
(topic! 'proj-in-fun 'plumbing)
(topic! 'class-in-quotient 'plumbing)
(topic! 'class-self 'plumbing)

;;; ===== inequalities & order =====
(topic! 'rr-lt-implies-le 'inequalities)
(topic! 'rr-lt-trans 'inequalities)
(topic! 'rr-le-trans 'inequalities)
(topic! 'rr-le-trans-c 'inequalities)
(topic! 'rr-lt-le-trans 'inequalities)
(topic! 'rr-le-lt-trans 'inequalities)
(topic! 'rr-le-add 'inequalities)
(topic! 'rr-add-nonneg 'inequalities)
(topic! 'rr-lt-add 'inequalities)
(topic! 'rr-le-scale-nonneg 'inequalities)
(topic! 'rr-lt-scale-pos 'inequalities)
(topic! 'rr-le-abs 'inequalities)
(topic! 'rr-abs-bound 'inequalities)
(topic! 'rr-abs-reverse-triangle 'inequalities)
(topic! 'rr-sq-nonneg 'inequalities)
(topic! 'rr-le-from-diff-nonneg 'inequalities)
(topic! 'rr-double-nonneg 'inequalities)
(topic! 'nn-pair-upper-bound 'inequalities)
(topic! 'rr-pos-halvable 'inequalities)
(topic! 'rr-pos-shrink 'inequalities)
(topic! 'rr-young-2 'inequalities)
(topic! 'rr-amgm-2 'inequalities)
(topic! 'rr-qm-am-2 'inequalities)
(topic! 'rr-cauchy-schwarz-2 'inequalities)
(topic! 'rr-bernoulli 'inequalities)
(topic! 'bdd-fn-nonneg 'inequalities)
(topic! 'bdd-fn-lt-one 'inequalities)
(topic! 'bdd-fn-le-arg 'inequalities)
(topic! 'bdd-fn-mono 'inequalities)
(topic! 'bdd-fn-subadd 'inequalities)
(topic! 'rpow-mono-base 'inequalities)
(topic! 'rpow-mono-exp-ge1 'inequalities)
(topic! 'rpow-mono-exp-le1 'inequalities)
(topic! 'amgm-2-sqrt 'inequalities)
(topic! 'young-inequality 'inequalities)
(topic! 'bernoulli-rpow 'inequalities)
(topic! 'finsum-sq-nonneg 'inequalities)
(topic! 'finsum-le-termwise 'inequalities)
(topic! 'finsum-abs-triangle 'inequalities)
(topic! 'cauchy-schwarz-finite 'inequalities)
(topic! 'cauchy-schwarz-sqrt 'inequalities)
(topic! 'minkowski-l2 'inequalities)
(topic! 'holder-finite 'inequalities)
;; order-lemmas.scm sign/difference/negation facts (Caratheodory MVT arc) --
;; finite order/sign deductions, no completeness.
(topic! 'rr-le-diff-nonpos 'inequalities)
(topic! 'rr-lt-diff-pos 'inequalities)
(topic! 'rr-lt-diff-neg 'inequalities)
(topic! 'rr-prod-nonpos-pos 'inequalities)
(topic! 'rr-prod-nonpos-neg 'inequalities)
(topic! 'rr-le-neg 'inequalities)
(topic! 'rr-neg-eq-zero 'inequalities)
;; rolle-proof.scm order helpers: trichotomy, betweenness (eps-density), and the
;; two interior-position facts (a strict extremum above equal endpoints is
;; interior -- order logic over the function values, not a limit/completeness).
(topic! 'rr-le-cases 'inequalities)
(topic! 'rr-le-ne-lt 'inequalities)
(topic! 'rr-midpoint-between 'inequalities)
(topic! 'max-val-strict-interior 'inequalities)
(topic! 'min-val-strict-interior 'inequalities)

;;; ===== combinatorial constructions =====
(topic! 'injection-extension-recurrence 'combinatorial)
(topic! 'permutations-zero 'combinatorial)
(topic! 'permutation-recurrence 'combinatorial)
(topic! 'choose-n-0 'combinatorial)
(topic! 'choose-0-succ 'combinatorial)
(topic! 'choose-succ 'combinatorial)
(topic! 'injection-count-falling 'combinatorial)
(topic! 'choose-times-factorial 'combinatorial)(topic! 'cover-block-step 'combinatorial)
;; block-family-combinatorial is now PROVEN (block-family-combinatorial-proof.scm),
;; not a support -- no category entry.
(topic! 'tb-has-eps-cauchy-subseq 'combinatorial)
(topic! 'tb-block-step 'combinatorial)
(topic! 'tb-rad-ball-cover 'combinatorial)
(topic! 'cauchy-block-estimate 'combinatorial)
(topic! 'block-family 'combinatorial)(topic! 'strictly-mono-ge-id 'combinatorial)
(topic! 'null-rr-seq-exists 'combinatorial)
(topic! 'dc-on-nn 'combinatorial)
(topic! 'dc-on-nn-pred 'combinatorial)
;; diagonalization is now PROVEN (not a support); its three generic leaves:
(topic! 'nn-step-strictly-mono 'combinatorial)
(topic! 'nn-nested-subset-chain 'combinatorial)
(topic! 'inf-subset-nn-unbounded 'combinatorial)
(topic! 'pigeonhole-infinite 'combinatorial)
(topic! 'convergence-block-tower 'combinatorial)
(topic! 'coordinatewise-diagonal-subseq 'combinatorial)
(topic! 'subsequence-capture 'combinatorial)
(topic! 'nn-enum-spec 'combinatorial)
(topic! 'well-ordering-principle 'combinatorial)
(topic! 'ord-well-ordered 'combinatorial)
(topic! 'power-insert-cover 'combinatorial)
(topic! 'power-insert-disjoint 'combinatorial)
(topic! 'prod-of-sums-expansion 'combinatorial)
(topic! 'finsum-fubini 'combinatorial)
(topic! 'finsum-reindex 'combinatorial)
(topic! 'sum-ag-permutation-invariance 'combinatorial)
(topic! 'finsum-comm-monoid-permutation-invariance 'combinatorial)
(topic! 'finsum-well-defined 'combinatorial)
(topic! 'finsum-comm-monoid-well-defined 'combinatorial)
(topic! 'chosen-centre-is-centre 'combinatorial)
(topic! 'finite-ball-subcover-r-net 'combinatorial)

;;; ===== real analysis: limits, series, completeness =====
(topic! 'ratio-test-converges 'analysis)
(topic! 'ps-abs-term 'analysis)
(topic! 'ps-absolute-implies-convergent 'analysis)
(topic! 'ps-partial-sum-as-series 'analysis)
(topic! 'ps-converges-as-series 'analysis)
(topic! 'geometric-partial-sum 'analysis)
(topic! 'geometric-series-converges-to 'analysis)
(topic! 'series-partial-sum-abs-le 'analysis)
(topic! 'series-cauchy-criterion 'analysis)
(topic! 'absolute-summable-implies-summable 'analysis)
(topic! 'summable-bound-implies-cauchy 'analysis)
(topic! 'summable-bound-converges 'analysis)
(topic! 'esum-finite-iff-bounded 'analysis)
(topic! 'cauchy-cluster-converges 'analysis)
(topic! 'cauchy-rapid-subsequence 'analysis)

;;; ===== algebraic & ring-structure facts =====
(topic! 'ring-power-zero 'algebra)
(topic! 'ring-power-one 'algebra)
(topic! 'ring-power-add 'algebra)
(topic! 'ring-power-mult 'algebra)
(topic! 'ring-power-succ 'algebra)
(topic! 'rpow-zero 'algebra)
(topic! 'rpow-one 'algebra)
(topic! 'rpow-add 'algebra)
(topic! 'rpow-mul-base 'algebra)
(topic! 'rpow-pow 'algebra)
(topic! 'rpow-neg 'algebra)
(topic! 'rpow-nat 'algebra)
(topic! 'rpow-zero-base 'algebra)
(topic! 'rpow-zero-zero 'algebra)
;; sqrt-nonneg / sqrt-sq / sqrt-of-sq / sqrt-mono / sqrt-mul left this file on
;; 2026-08-17: they stopped being supports of real-powers.scm and became
;; theorems of theorem-library/sqrt-defined.scm, which files its own topics.
;; sqrt-rpow stays -- it is still a support, being a claim about RPOW.
(topic! 'sqrt-rpow 'algebra)
(topic! 'finsum-add 'algebra)
(topic! 'finsum-ring-distrib-left 'algebra)
(topic! 'finsum-ring-scalar-zz 'algebra)
(topic! 'finsum-insert 'algebra)
(topic! 'prod-ring-insert 'algebra)
(topic! 'sum-set-left-scalar 'algebra)
(topic! 'sum-set-right-scalar 'algebra)
(topic! 'euclidean-ring-has-gauge 'algebra)
(topic! 'gauge-is-degree 'algebra)
(topic! 'ideal-elt-in-carrier 'algebra)
(topic! 'principal-ideal-in-ideal 'algebra)
(topic! 'euclidean-ideal-has-generator 'algebra)
;; matrices over a ring (matrix.scm): the tabulation bridge + multiplication.
(topic! 'interval-membership 'plumbing)
(topic! 'interval-in-set 'plumbing)
(topic! 'interval-card 'plumbing)
(topic! 'entry-in-carrier 'plumbing)
(topic! 'matof-in-mat 'plumbing)
(topic! 'entry-of-matof 'plumbing)
(topic! 'matrix-entry-extensionality 'algebra)
(topic! 'matmul-type 'algebra)
(topic! 'matmul-entry 'algebra)
(topic! 'entry-of-identmat 'algebra)
(topic! 'identmat-type 'algebra)
(topic! 'finsum-single-support 'algebra)
(topic! 'ras-carr 'plumbing)
(topic! 'ras-id 'plumbing)
;; the matrix-ring axioms (obligations toward mat-ring-is-ring)
(topic! 'matadd-type 'algebra)
(topic! 'matneg-type 'algebra)
(topic! 'zeromat-type 'algebra)
(topic! 'matadd-comm 'algebra)
(topic! 'matadd-assoc 'algebra)
(topic! 'matadd-zero-left 'algebra)
(topic! 'matadd-neg-left 'algebra)
(topic! 'matmul-assoc 'algebra)
(topic! 'identmat-left-identity 'algebra)
(topic! 'identmat-right-identity 'algebra)
(topic! 'matmul-left-dist-guarded 'algebra)
(topic! 'matmul-right-dist-guarded 'algebra)
(topic! 'mat-ring-is-ring 'algebra)

;;; ===== metric topology & continuity =====
(topic! 'ball-cover-is-open-cover 'topology)
(topic! 'compact-iff-seq-compact 'topology)
(topic! 'seq-compact-countable-product 'topology)
(topic! 'compact-implies-totally-bounded 'topology)
(topic! 'compact-implies-complete 'topology)
(topic! 'compact-seq-has-cluster 'topology)
(topic! 'empty-is-open 'topology)
(topic! 'carrier-is-open 'topology)
(topic! 'ball-is-open 'topology)
(topic! 'union-of-opens-open 'topology)
(topic! 'inter-of-opens-open 'topology)
(topic! 'continuous-implies-open-preimage 'topology)
(topic! 'open-preimage-implies-continuous 'topology)
(topic! 'preimage-complement 'topology)
(topic! 'continuous-implies-closed-preimage 'topology)
(topic! 'closed-preimage-implies-continuous 'topology)
(topic! 'ball-mem-from-le 'topology)
(topic! 'ball-center-in 'topology)
(topic! 'ball-2r-triangle 'topology)
(topic! 'continuous-is-continuous-at 'topology)
(topic! 'uniformly-continuous-is-continuous 'topology)
;;; ===== metric-space + quotient constructions =====
(topic! 'bdd-metric-distance 'constructions)
(topic! 'bdd-metric-is-metric-space 'constructions)
(topic! 'bdd-metric-bounded 'constructions)
(topic! 'bdd-metric-id-bicontinuous 'constructions)
(topic! 'rr-bounded-ms-is-metric-space 'constructions)
(topic! 'rr-bounded-ms-bounded 'constructions)
(topic! 'rr-bounded-equivalent 'constructions)
(topic! 'product-weighted-summable 'constructions)
(topic! 'product-is-metric-space 'constructions)
(topic! 'product-projection-continuous 'constructions)
(topic! 'product-convergence-coordinatewise 'constructions)
(topic! 'product-weights-equivalent 'constructions)
(topic! 'product-metric-default-summable 'constructions)
(topic! 'completion-is-metric-space 'constructions)
(topic! 'completion-is-complete 'constructions)
(topic! 'embed-in-fun 'constructions)
(topic! 'embed-isometry 'constructions)
(topic! 'nag-metric-distance 'constructions)
(topic! 'nag-metric-space-is-metric-space 'constructions)
(topic! 'nf-metric-distance 'constructions)
(topic! 'nf-metric-space-is-metric-space 'constructions)

;;; ===== set & quotient constructions =====
;;; The setoid/quotient construction (equivalence classes, descent, the
;;; universal property).  Why not grind: mechanical verification of the
;;; quotient's defining mapping property over the CLASS/QUOTIENT/DESCEND
;;; machinery.  (The plumbing-grade quotient TYPING slices -- class-is-set,
;;; quotient-is-set, proj-in-fun, class-in-quotient, class-subset-carrier,
;;; class-self -- stay under `plumbing' by KIND, not topic.)
(topic! 'cauchy-setoid-is-setoid 'set-quotient)
(topic! 'class-eq-iff 'set-quotient)
(topic! 'class-disjoint 'set-quotient)
(topic! 'descend-computes 'set-quotient)
(topic! 'descend-in-fun 'set-quotient)
(topic! 'quotient-universal 'set-quotient)
