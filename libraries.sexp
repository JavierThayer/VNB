;;; libraries.sexp -- THE LIBRARIES of the VNB tree (the user, notes-61, 2026-10-06).
;;;
;;; A library is a declared set of theorem-library/ and structure-library/ files
;;; with declared IMPORTS.  Read at load by libraries.scm; the gate `library-gate!'
;;; (run-load-end!) checks that a theorem cites, and a statement uses the
;;; vocabulary of, only its own library and the import closure.  The book
;;; reference/library-book.tex (library-book.scm) has one part per library, in
;;; the order below, which must be a topological order of the imports.
;;; Every theorem-library/ and structure-library/ file of load.scm's *vnb-files*
;;; must appear in exactly one `files' list or in `exempt'.  File names are the
;;; load-list names (no .scm).  Edit by hand; keep a file under the library its
;;; MATHEMATICS belongs to and let the gate report the lemma that should move.

(library core
  (title "Foundations")
  (about "Logic and sets; the number systems NN, ZZ, QQ, RR and CC with their arithmetic and order; tuples and lists; functions, bijections and intervals; finite sums; cardinality and ordinals; choice (Zermelo, Zorn); the combinatorial lemmas. Every other book stands on this one.")
  (imports)
  (files
    "theorem-library/singleton-membership"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/card-cartesian-nn"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/rr-mul-le-cancel"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/rr-zero-mul"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/singleton-is-set"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/cartesian-nth"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/nn-cancel"
    "number-systems"           ; the arithmetic base (root file): the primitive shelf of NN, ZZ, QQ, RR, CC
    "structure-library/references"
    "structure-library/operation-properties"
    "theorem-library/axioms"
    "structure-library/set-basics"
    "structure-library/set-vocabulary"
    "structure-library/intersection-of"
    "structure-library/compose"
    "structure-library/id-fun"
    "structure-library/linear-arith"
    "structure-library/ineq-oracle"
    "structure-library/sos-arith"
    "structure-library/sos-oracle"
    "structure-library/nn-arith"
    "structure-library/list-recursion"
    "structure-library/sqn"
    "theorem-library/sqn-laws"    ; 2026-11-13
    "structure-library/zz-arith"
    "structure-library/order-predicates"
    "structure-library/nn-minus"
    "structure-library/order-lemmas"
    "structure-library/scalar-inequalities"
    "structure-library/real-powers"
    "structure-library/qq-fractions"
    "structure-library/complex"
    "structure-library/reduce"
    "structure-library/ordinals"
    "structure-library/bijection"
    "structure-library/cardinality"
    "structure-library/injection"
    "structure-library/compose-typing"
    "structure-library/inf-subsets"
    "theorem-library/dc-on-nn"
    "theorem-library/pigeonhole"
    "theorem-library/diagonalization-lemmas"
    "structure-library/finsum"
    "theorem-library/sum-ag-permutation-invariance"
    "theorem-library/finsum-fubini"
    "structure-library/matrix"
    "structure-library/user-additions"
    "structure-library/definitional-reclass"
    "theorem-library/succ-nn-ord"
    "theorem-library/ord-segment-zero-no-members"
    "theorem-library/ord-segment-trans"
    "theorem-library/ord-segment-self"
    "theorem-library/fin-enum-is-bijection"
    "theorem-library/finsum-well-defined"
    "theorem-library/union-empty-left"
    "theorem-library/finsum-empty"
    "theorem-library/finsum-singleton"
    "theorem-library/finsum-comm-monoid"
    "theorem-library/finsum-additive"
    "theorem-library/founder-warrants"
    "theorem-library/ord-well-ordered-proof"
    "theorem-library/equality-basics"
    "theorem-library/factorial-in-nn"
    "theorem-library/rake-compose-typing"
    "theorem-library/co-eq-lt-trans"
    "theorem-library/interval-basics"
    "theorem-library/interval-mem-intro"
    "theorem-library/ord-segment-nn-succ-proof"
    "theorem-library/ord-segment-nn-subset-proof"
    "theorem-library/inf-subsets-is-set"
    "theorem-library/binary-minus-laws"
    "theorem-library/fun-apply-type-proof"
    "theorem-library/image-subset-codomain"
    "theorem-library/rake-dc-on-nn"
    "theorem-library/compose-apply-proof"
    "theorem-library/id-fun-laws"
    "theorem-library/pair-tuple-sethood"
    "theorem-library/pair-laws"          ; cartesian-nth, cartesian-pair-eq, pair-in-cartesian-parts, node-pair-injective (CLEANUP-1, 2026-10-25)
    "theorem-library/nn-order-ord"
    "theorem-library/nn-not-le-succ-le"
    "theorem-library/nn-order-basics"
    "theorem-library/mat-basics"
    "theorem-library/nn-pos-of-nonzero"
    "theorem-library/interval-membership"
    "theorem-library/nn-not-lt-le-proof"
    "theorem-library/rr-order-basics"
    "theorem-library/co-order-trans-guarded"
    "theorem-library/pos-rr-bridges"
    "theorem-library/rr-abs-basics"
    "theorem-library/rr-max-basics"
    "theorem-library/rr-min-basics"
    "theorem-library/cc-real-imag"
    "theorem-library/rr-recip-order"
    "theorem-library/pos-rr-of-lt"
    "theorem-library/rr-halving"
    "theorem-library/rr-order-bundle"
    "theorem-library/rr-le-all-pos"
    "theorem-library/subset-lemmas"
    "theorem-library/fun-image-set"
    "theorem-library/rake-inverse-bij"
    "theorem-library/nn-parity-proof"
    "theorem-library/nn-pred"
    "theorem-library/ord-segment-arith"
    "theorem-library/finite-surgery"
    "theorem-library/pigeonhole-segments"
    "theorem-library/enum-append"
    "theorem-library/union-laws"
    "structure-library/bijection-derived"
    "theorem-library/bijection-identity-proof"
    "theorem-library/card-defined"
    "theorem-library/card-finite"
    "theorem-library/ord-no-injection"
    "theorem-library/zen-step"
    "theorem-library/rake-zermelo"
    "theorem-library/rake-ord-pigeonhole"
    "theorem-library/rake-card-star-laws"
    "theorem-library/card-laws"
    "theorem-library/card-singleton-proof"
    "theorem-library/rake-fin-enum"
    "theorem-library/difference-laws"
    "theorem-library/intersection-of-laws"
    "theorem-library/rake-complement-laws"
    "theorem-library/rake-fun-codomain"
    "theorem-library/rake-rr-order-leaves"
    "theorem-library/rr-sup-approx"
    "theorem-library/nn-unbounded-in-rr"
    "theorem-library/nn-recip-succ-small"
    "theorem-library/lambda-slot-apply"
    "theorem-library/nn-mod3-proof"
    "theorem-library/nn-order-via-rr"
    "theorem-library/rake-intervals"
    "theorem-library/zz-order"
    "theorem-library/zz-parity-proof"
    "theorem-library/nn-pos-is-succ"
    "theorem-library/nn-order-proof"
    "theorem-library/makeset-basics"
    "theorem-library/empty-cardinality"
    "theorem-library/tuples-induction"
    "theorem-library/tuple-extensionality"
    "theorem-library/la-z5-card"
    "theorem-library/tuple-tabulation"
    "theorem-library/matof-in-mat"
    "theorem-library/makeset-card-bound"
    "theorem-library/card-subset-nn"
    "theorem-library/card-image-finite"
    "theorem-library/interval-card-in-nn"
    "theorem-library/nn-finite-subset-bounded"
    "theorem-library/card-inequalities"
    "theorem-library/rake-combinatorics2"
    "theorem-library/rake-choose-succ"
    "theorem-library/nn-infinite"
    "theorem-library/fin-subsets"
    "theorem-library/nn-pairing"
    "theorem-library/nn-nested-subset-chain-proof"
    "structure-library/order-zorn"
    "theorem-library/injective-star"
    "theorem-library/zorn-proof"
    "theorem-library/zorn-route-two"
    "theorem-library/nn-least-element"
    "theorem-library/pair-self-cartesian3"   ; pair-self-member, pair-self-eq, cartesian3-set (moved from strand-messages-laws, META-W1 2026-10-16)
    "theorem-library/interval-widen"
    "theorem-library/rake-finsum-typing-nn"
    "structure-library/rr-ineq"
    "theorem-library/axioms"
  
    "structure-library/rabasics-vocab"   ; wave 2026-10-26/27
    "theorem-library/rabasics-order"   ; wave 2026-10-26/27
    
    "theorem-library/rr-not-lt-ge"   ; wave 2026-11-09/10
    "theorem-library/difference-subset"   ; wave 2026-11-09/10
    "theorem-library/sep-congruence"   ; wave 2026-11-09/10
    "theorem-library/unique-choice"   ; wave 2026-11-09/10
    "theorem-library/union-subset-both"   ; wave 2026-11-09/10
    "theorem-library/th3-sort"   ; wave 2026-11-09/10
    ))

(library algebra
  (title "Algebra")
  (about "Semigroups, monoids, groups, rings, integral domains and fields; ideals, Euclidean rings and Bezout; polynomials and monoid algebras; setoids, quotients and ringoids; homomorphisms, categories and views.")
  (imports core)
  (files
    "theorem-library/prod-ring-succ"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/field-one-ne"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/zz-divides-basics"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/zz-ring-arith"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/nn-integral"
    "structure-library/semigroup"
    "structure-library/monoid"
    "structure-library/group"
    "structure-library/abelian-group"
    "structure-library/ring"
    "structure-library/setoid"
    "structure-library/ringoid"
    "structure-library/ring-simplify"
    "structure-library/comm-ring-simplify"
    "structure-library/commutative-ring"
    "structure-library/integral-domain"
    "structure-library/field"
    "structure-library/euclidean-ring"
    "structure-library/ideal"
    "structure-library/views"
    "structure-library/numeric-instances"
    "structure-library/zz-divisibility"
    "structure-library/monoid-power"
    "structure-library/zz-action"
    "structure-library/ring-power"
    "structure-library/sequences"
    "structure-library/finprod"
    "structure-library/polynomial"
    "structure-library/la-z6-vocab"
    "structure-library/prod-of-sums"
    "structure-library/binomial"
    "theorem-library/poly-membership"
    "theorem-library/ag-view-read-offs"
    "theorem-library/rake-setoid"
    "theorem-library/rake-asm-2"
    "theorem-library/bt-shims"
    "structure-library/subtype-laws"
    "structure-library/is-set-laws"   ; W1I 2026-11-06: the generated is-X-is-set (cross-cutting)
    "theorem-library/finsum-type-proof"
    "theorem-library/finsum-single-support"
    "structure-library/integral-domain-laws"
    "theorem-library/zz-ring-is-ring"
    "theorem-library/zz-integral-domain"
    "theorem-library/nn-add-monoid"
    "theorem-library/cancellation"
    "theorem-library/ring-zero-one-power"
    "theorem-library/comb-kk-laws"
    "theorem-library/zz-division"
    "theorem-library/rake-algebra"
    "theorem-library/rake-algebra2"
    "theorem-library/rake-monoid-laws"
    "theorem-library/rake-zz-act"
    "theorem-library/rake-ringoid-additive"
    "theorem-library/rake-finsum-typing"
    "theorem-library/rake-finsum-welldef"
    "theorem-library/finsum-insert"
    "theorem-library/field-ring-view"
    "theorem-library/hom-laws"
    "theorem-library/hom-kinds"
    "theorem-library/hom-functors"
    "theorem-library/hom-views"
    "theorem-library/qq-field-is-field"
    "theorem-library/rake-finsum-laws"
    "theorem-library/rake-finsum-laws2"
    "theorem-library/rake-finsum-core"
    "theorem-library/rake-finsum-cm-ptwise"
    "theorem-library/rake-finsum-fubini-c"
    "theorem-library/rake-combinatorics"
    "theorem-library/rake-finsum-union"
    "theorem-library/rake-finsum-cm-union"
    "theorem-library/rake-sum-set-defined"
    "theorem-library/rake-prod-set-defined"
    "theorem-library/rake-sum-set-scalar"
    "theorem-library/fin-subset-monoid"
    "theorem-library/rake-algebra3"
    "theorem-library/poly-tail-zero"
    "theorem-library/finsum-fiber"
    "theorem-library/monalg-laws"
    "theorem-library/poly-zero"
    "theorem-library/monalg-is-ring"
    "theorem-library/la-z6-pullback"
    "theorem-library/rake-prod-of-sums"
    "theorem-library/rake-monalg-comm"
    "theorem-library/la-z6-mpoly"
    "structure-library/poly-degree"
    "theorem-library/poly-degree-laws"
    "theorem-library/gauge-is-degree"
    "theorem-library/euclidean-ideal-generator-proof"
    "theorem-library/zz-bezout-proof"
    "theorem-library/euclidean-division-proof"
    "theorem-library/binomial-proof"
    "theorem-library/poly-is-ring-proof"
    "theorem-library/ringoid-setoid-proof"
    "theorem-library/rake-ringoid"
    "theorem-library/rake-ringoid-quotient"
    "structure-library/functoriality"
  
    "structure-library/zz-nt-vocab"   ; wave 2026-10-26/27
    "theorem-library/zz-number-theory"   ; wave 2026-10-26/27
    "structure-library/catools-gal-vocab"   ; wave 2026-10-26/27
    "theorem-library/catools-gal-b1"   ; wave 2026-10-26/27
    "structure-library/gal-ufd-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-ufd"   ; wave 2026-10-26/27
    "structure-library/gal-poly-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-poly"   ; wave 2026-10-26/27
    "theorem-library/gal-interp"   ; wave 2026-10-26/27
    "structure-library/gal-gcd-vocab"   ; wave 2026-10-26/27
    "structure-library/gal-char-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-char"   ; wave 2026-10-26/27
    "theorem-library/tg-group"   ; wave 2026-10-26/27
    "structure-library/cg2-vocab"   ; wave 2026-10-26/27
    "theorem-library/cg2-setprod"   ; wave 2026-10-26/27
    "theorem-library/cg4-gpow"   ; wave 2026-10-26/27
    "theorem-library/zz-primes"   ; wave 2026-10-26/27
    "structure-library/group-cosets-vocab"   ; wave 2026-10-26/27
    "structure-library/group-zpow-vocab"   ; wave 2026-10-26/27
    "theorem-library/group-zpow"   ; wave 2026-10-26/27
    "theorem-library/group-cosets"   ; wave 2026-10-26/27
    "theorem-library/cyclic-product"   ; wave 2026-10-26/27
    "theorem-library/group-family-product"   ; wave 2026-10-26/27
    
    "theorem-library/finsum-cm-ptwise-laws"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-geom"   ; wave 2026-11-09/10
    "theorem-library/ccr4c-finite-char"   ; wave 2026-11-09/10
    ))

(library linear-algebra
  (title "Linear Algebra")
  (about "Modules and vector spaces; matrices, elementary operations, determinants and the Smith normal form; spans, submodules, bases and rank; finite-dimensional spaces.")
  (imports algebra)
  (files
    "structure-library/module"
    "structure-library/finite-dimensional"
    "structure-library/transpose"
    "structure-library/elementary-matrix"
    "structure-library/mat-equiv"
    "structure-library/determinant"
    "structure-library/la-det-vocab"
    "structure-library/la-elem-vocab"
    "structure-library/la-z-vocab"
    "structure-library/la-z2-vocab"
    "structure-library/la-z3-vocab"
    "structure-library/la-z4-vocab"
    "structure-library/la-z5-vocab"
    "structure-library/mod-seq"
    "theorem-library/entry-in-carrier"
    "theorem-library/qq-vs-exemplification"
    "theorem-library/rake-border-entry"
    "theorem-library/rake-border-siblings"
    "theorem-library/mat-typing-bundle"
    "theorem-library/rake-mat-typing"
    "theorem-library/rake-det-small"
    "theorem-library/rake-mat-ring-readoffs"
    "theorem-library/matmul-entry-proof"
    "theorem-library/matunit-matact-type"
    "theorem-library/lam-fun-bricks"
    "theorem-library/rake-identmat"
    "theorem-library/rake-generates-coeff"
    "theorem-library/rake-smith-leaves"
    "theorem-library/module-zero-act"
    "theorem-library/triple-entry-proof"
    "theorem-library/matmul-assoc-proof"
    "theorem-library/elem-entry-readoffs"
    "theorem-library/rake-matrix-laws"
    "theorem-library/mat-ring-proof"
    "theorem-library/matunit-shift-proof"
    "theorem-library/elem-actions-proof"
    "theorem-library/elem-inverses-proof"
    "theorem-library/elem-row-actions-proof"
    "theorem-library/det-rows"
    "theorem-library/det-mul"
    "theorem-library/pivot-col-reduce-proof"
    "theorem-library/pivot-row-reduce-proof"
    "theorem-library/mat-equiv-proof"
    "theorem-library/min-degree-entry-proof"
    "theorem-library/smith-proof"
    "theorem-library/class-min-pivot-proof"
    "theorem-library/smith-clear-proof"
    "theorem-library/clear-first-row-proof"
    "theorem-library/clear-first-col-proof"
    "theorem-library/matact-summand-type-le-proof"
    "theorem-library/border-mult-proof"
    "theorem-library/border-assembly-proof"
    "theorem-library/bordered-eq-border-proof"
    "theorem-library/det-alternating-form"
    "theorem-library/det-multiplicative"
    "theorem-library/det-transpose"
    "theorem-library/clear-pivot-cross-proof"
    "theorem-library/smith-diagonalization-proof"
    "theorem-library/smith-staircase-proof"
    "theorem-library/matact-row-linear-proof"
    "theorem-library/span-bricks-proof"
    "theorem-library/span-bricks2-proof"
    "theorem-library/lastcoeff-ideal-proof"
    "theorem-library/spans-submodule-fg-proof"
    "theorem-library/submodule-free"
    "theorem-library/submodule-fg-proof"
    "theorem-library/matact-assoc-proof"
    "theorem-library/mod-basis-proof"
    "theorem-library/inverse-invertible-proof"
    "theorem-library/la-det-adjoint"
    "theorem-library/la-elem-gen"
    "theorem-library/la-z6-col"
    "theorem-library/module-laws"
    "theorem-library/la-z-sdet"
    "theorem-library/la-z-gcd"
    "theorem-library/la-z-elem"
    "theorem-library/la-z2-action"
    "theorem-library/la-z2-norm"
    "theorem-library/la-z2-diag"
    "theorem-library/la-z2-principal"
    "theorem-library/la-z3-smith"
    "theorem-library/la-z3-quotient"
    "theorem-library/la-z3-dsum"
    "theorem-library/la-z3-struct"
    "theorem-library/la-z4-free"
    "theorem-library/la-z4-dsum"
    "theorem-library/la-z4-exist"
    "theorem-library/la-z4-schanuel"
    "theorem-library/la-z4-unique"
    "theorem-library/la-z5-norm"
    "theorem-library/la-z5-zzmod"
    "theorem-library/la-z5-dsumcard"
    "theorem-library/la-z5-card52"
    "theorem-library/spans-transport-proof"
    "theorem-library/rake-asm-b4"
    "theorem-library/rank-bound-proof"
  
    "theorem-library/gal-smith"   ; wave 2026-10-26/27
    "structure-library/gal-charpoly-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-charpoly"   ; wave 2026-10-26/27
    "structure-library/gal-op-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-op"   ; wave 2026-10-26/27
    "structure-library/gal-ch-vocab"   ; wave 2026-10-26/27
    "theorem-library/gal-op2"   ; wave 2026-10-26/27
    "theorem-library/gal-ch"   ; wave 2026-10-26/27
    
    "structure-library/qag-vocab"   ; wave-2 2026-10-30
    "theorem-library/qag-laws"   ; wave-2 2026-10-30
    
    "theorem-library/ccr-adj-unit"   ; wave 2026-11-09/10
    "structure-library/ring-pow-vocab"   ; wave 2026-11-09/10
    "theorem-library/ring-pow"   ; wave 2026-11-09/10
    "theorem-library/ring-pow-form"   ; wave 2026-11-09/10
    "theorem-library/zz-pow-via-ring-pow"   ; wave 2026-11-09/10
    "theorem-library/poly-eval-mul"   ; wave 2026-11-11
    ))

(library analysis
  (title "Analysis")
  (about "Metric spaces and their topology, completeness, compactness and continuity; normed fields and normed vector spaces; sequences and series of real and complex numbers; the calculus of one real variable on an interval: derivatives, the mean value theorem, Taylor, antiderivatives, regulated functions and the integral; roads and line integrals; Ascoli, Baire, Hahn-Banach, Bernstein.")
  (imports linear-algebra)
  (files
    "theorem-library/cvx-alg"   ; wave 2026-10-26/27 (analysis: cites the NVS laws)
    "structure-library/cvx-vocab"   ; wave 2026-10-26/27 (analysis: cites the NVS laws)
    "theorem-library/cc-power-add"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/nn-power-two-bound"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/subseq-fun-typing"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/subset-rr-power"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/rr-pos-star-order-lemmas"   ; wave 2026-10-26/27: moved lemmas
    "theorem-library/cg4-extreme"   ; wave 2026-10-26/27 (analysis: IS-CONVEX-SUBSET / IS-EXTREME-POINT are analysis vocabulary)
    "theorem-library/cvx-hull"   ; wave 2026-10-26/27 (analysis: IS-CONVEX-SUBSET / IS-EXTREME-POINT are analysis vocabulary)
    "theorem-library/normed-field-ring-view"
    "theorem-library/block-family-combinatorial-proof"
    "structure-library/metric-space"
    "structure-library/metric-topology"
    "structure-library/metric-completeness"
    "structure-library/metric-continuity"
    "structure-library/metric-open-sets"
    "structure-library/metric-connected"
    "structure-library/top-space"
    "structure-library/compactness"
    "structure-library/top-continuity"
    "structure-library/separable"
    "structure-library/normed-field"
    "structure-library/normed-ag"
    "structure-library/normed-field-metric"
    "structure-library/normed-ag-metric"
    "structure-library/normed-vector-space"
    "structure-library/nvs-metric"
    "structure-library/linear-functional"
    "structure-library/dual-space"
    "structure-library/metric-subspace"
    "structure-library/product2-vocab"
    "theorem-library/product2-laws"
    "structure-library/diff-on"
    "structure-library/extreme-value"
    "structure-library/derivative"
    "structure-library/cc-coords"
    "structure-library/antiderivative"
    "structure-library/complex-inner-product"
    "structure-library/bounded-metric"
    "structure-library/trunc-metric"
    "structure-library/pseudometric"
    "structure-library/metric-completion"
    "structure-library/extended-reals"
    "structure-library/extended-reals-pos"
    "structure-library/nth-deriv"
    "structure-library/block-family-combinatorial"
    "structure-library/subsequence-capture"
    "structure-library/cauchy-subsequence"
    "theorem-library/analysis-inequalities"
    "structure-library/extended-sum"
    "structure-library/extended-arith"
    "structure-library/summability"
    "structure-library/power-series"
    "theorem-library/series-order-lemmas"
    "theorem-library/summable-cauchy"
    "structure-library/product-metric"
    "structure-library/c-metric-space"
    "structure-library/seq-compact-product"
    "theorem-library/subseq-apply"
    "theorem-library/bdd-metric-carrier"
    "theorem-library/rake-analysis2"
    "theorem-library/rr-star-order-minimal"   ; EXT-ORDER, wired 2026-10-27 (batch 0)
    "theorem-library/rake-infinity-points"
    "theorem-library/rake-rr-pos-star"
    "theorem-library/rake-eplus-defined"
    "theorem-library/rake-etimes-defined"
    "theorem-library/discrete-space"
    "theorem-library/op-typing"
    "theorem-library/rr-is-normed-field"
    "theorem-library/rr-nvs-exemplification"
    "theorem-library/rake-extended-order"
    "theorem-library/rake-esup-defined"
    "theorem-library/rake-rr-pos-star-monoid"
    "theorem-library/rake-esum-defined"
    "theorem-library/rake-esum-finite"
    "theorem-library/ball-cover-lemmas"
    "structure-library/metric-laws"
    "theorem-library/ball-is-open"
    "theorem-library/rake-compact-complete"
    "theorem-library/rake-compact-cluster"
    "theorem-library/rake-balls"
    "theorem-library/metric-connected-laws"
    "theorem-library/metric-subspace-laws"
    "theorem-library/compact-subspace"
    "theorem-library/rake-analysis-typing"
    "theorem-library/rake-cont-preimage"
    "theorem-library/pseudometric-laws"
    "theorem-library/bdd-metric-distance"
    "theorem-library/bdd-metric-basics"
    "theorem-library/rake-subseq-leaves"
    "theorem-library/rake-dc-consumers"
    "theorem-library/rake-compact-iff-seq-compact"
    "theorem-library/rake-seq-compact-tb"
    "theorem-library/rake-lebesgue-number"
    "theorem-library/rake-nn-enum"
    "theorem-library/rake-tb-leaves"
    "theorem-library/rake-tb-leaves-2"
    "theorem-library/diagonalization"
    "theorem-library/cauchy-subseq-proof"
    "theorem-library/rr-ms-dist"
    "theorem-library/rr-metric-space-proof"
    "theorem-library/trunc-metric-proof"
    "theorem-library/rr-complete-proof"
    "theorem-library/metric-limit-unique"
    "theorem-library/seq-limit-core"
    "structure-library/ascoli-arzela-statement"
    "theorem-library/ascoli-analytic-cores"
    "theorem-library/rake-open-sets"
    "theorem-library/ptwise-cauchy-unif"
    "theorem-library/ascoli-assembly"
    "theorem-library/unif-cauchy-limit"
    "theorem-library/ascoli-bridge"
    "structure-library/seminorm-hahn-banach"
    "structure-library/baire-category"
    "theorem-library/metric-closure-laws"
    "theorem-library/rake-baire"
    "structure-library/frechet-open-mapping"
    "structure-library/frechet-metric"
    "structure-library/frechet-banach-steinhaus"
    "theorem-library/subseq-convergence-proof"
    "theorem-library/subsqn-basics"
    "theorem-library/subsequence-principle"
    "theorem-library/rake-offbill-combinatorial"
    "theorem-library/rake-baire-2"
    "theorem-library/coord-block-estimate-proof"
    "theorem-library/sqrt2-proof"
    "theorem-library/sqrt3-proof"
    "theorem-library/continuity-basics"
    "theorem-library/neg-continuous"
    "theorem-library/continuity-sum"
    "theorem-library/continuity-product"
    "theorem-library/continuity-transfer"
    "theorem-library/continuity-sub"
    "theorem-library/continuity-scale"
    "theorem-library/continuity-compose"
    "theorem-library/continuity-recip"
    "theorem-library/continuity-algebra"
    "theorem-library/cont-agree-off-pt"
    "theorem-library/continuous-one-sided-sign"
    "theorem-library/differentiation"
    "theorem-library/diff-transfer"
    "theorem-library/deriv-sum-product"
    "theorem-library/chain-rule"
    "theorem-library/inverse-function"
    "theorem-library/higher-derivatives"
    "structure-library/little-o"
    "theorem-library/ccint-basics"
    "theorem-library/ivt-proof"
    "theorem-library/monotone-inverse"
    "theorem-library/sq-continuous"
    "theorem-library/sqrt-defined"
    "theorem-library/cc-magnitude"
    "theorem-library/cc-normed-field"
    "theorem-library/cc-metric-space-proof"
    "theorem-library/complex-inner-product-laws"
    "theorem-library/inner-product-inequalities"
    "theorem-library/rake-ip-normed-ag"
    "theorem-library/monotone-convergence-proof"
    "theorem-library/comparison-test-proof"
    "theorem-library/series-abs-triangle"
    "theorem-library/series-block-abs"
    "theorem-library/series-linearity"
    "theorem-library/bernstein-basis"
    "theorem-library/bernstein-moments"
    "theorem-library/series-cauchy-proof"
    "theorem-library/dominated-convergence"
    "theorem-library/cc-complete-proof"
    "theorem-library/series-abs-converges"
    "theorem-library/mono-le-limit"
    "theorem-library/limit-arithmetic"
    "theorem-library/ell-two"
    "theorem-library/dyadic-weights"
    "theorem-library/rake-inequalities"
    "theorem-library/deriv-power"
    "theorem-library/deriv-polynomial"
    "theorem-library/poly-antiderivative"
    "theorem-library/product-summable"
    "theorem-library/product-is-metric-space"
    "theorem-library/rake-block-tower"
    "theorem-library/rr-null-scale"
    "theorem-library/bdd-metric-convergence"
    "theorem-library/rake-metric-constructions"
    "theorem-library/rake-rr-bounded-ms"
    "theorem-library/rake-compact-equivalences"
    "theorem-library/rake-compact-fip"
    "theorem-library/compact-separable-proof"
    "theorem-library/rake-ascoli"
    "theorem-library/converges-dist-null"
    "theorem-library/sequential-continuity"
    "theorem-library/recip-succ-null"
    "theorem-library/product-convergence"
    "theorem-library/rake-diagonal-subseq"
    "theorem-library/tychonoff-proof"
    "theorem-library/rake-setoid2"
    "theorem-library/rake-completion-ms"
    "theorem-library/rake-completion-complete"
    "theorem-library/product-weights"
    "theorem-library/c-metric-summable"
    "theorem-library/c-metric-is-metric"
    "theorem-library/ccint-creep"
    "theorem-library/ccint-bounded"
    "theorem-library/uniform-continuity-ccint"
    "theorem-library/evt-proof"
    "theorem-library/heine-borel-baby"
    "theorem-library/evt-min-proof"
    "theorem-library/ccint-abs-bounded"
    "theorem-library/bernstein-density"
    "theorem-library/mean-value"
    "theorem-library/mvt-cluster-readoffs"
    "theorem-library/deriv-difference"
    "theorem-library/mvt-aux-guarded"
    "theorem-library/interior-extremum-proof"
    "theorem-library/rolle-proof"
    "theorem-library/mvt-proof"
    "theorem-library/deriv-constant-proof"
    "theorem-library/mvt-bounds-proof"
    "theorem-library/mvt-abs-bound"
    "theorem-library/continuity-local"
    "theorem-library/recip-star"
    "theorem-library/clamp"
    "theorem-library/seq-limit"
    "structure-library/regulated"
    "theorem-library/onesided-limits"
    "theorem-library/recip-succ-small"
    "theorem-library/continuous-is-regulated"
    "theorem-library/cauchy-criterion-left"
    "theorem-library/cauchy-criterion-right"
    "theorem-library/partition-locates-point"
    "theorem-library/uniform-limit-regulated"
    "theorem-library/uniform-limit-local"
    "theorem-library/diff-at-local"
    "theorem-library/generalized-mvt-proof"
    "theorem-library/deriv-monotone-proof"
    "theorem-library/taylor-proof"
    "theorem-library/rake-hb-leaves"
    "theorem-library/rake-dual-norm-spec"
    "theorem-library/nvs-module-view"
    "theorem-library/nvs-act-laws"
    "theorem-library/rake-norm-metrics"
    "theorem-library/nvs-norm-laws"
    "theorem-library/rake-hb-submodules"
    "theorem-library/rake-span-add-one-guarded"
    "theorem-library/rake-hb-leaves-2"
    "theorem-library/rake-hb-gap"
    "theorem-library/rake-hb-extend-construct"
    "theorem-library/rake-line-functional"
    "theorem-library/hahn-banach-proof"
    "theorem-library/noetherian-maximal-proof"
    "theorem-library/hahn-banach-full-proof"
    "structure-library/hahn-banach-sublinear"
    "theorem-library/hahn-banach-sublinear"
    "theorem-library/norm-as-sup-proof"
    "theorem-library/vector-taylor-proof"
    "theorem-library/rake-nf-norm"
    "theorem-library/diff-on-laws"
    "theorem-library/ms-continuity-algebra"
    "structure-library/riesz-markov-model"
    "theorem-library/riesz-markov-model"
    "theorem-library/metric-finite-subcover"
    "structure-library/positive-functional"
    "theorem-library/cont-fns-laws"
    "theorem-library/categories"
    "theorem-library/c-continuous-category"
    "theorem-library/diff-on-laws-2"
    "theorem-library/holomorphic-basics"
    "theorem-library/deriv-on-read-off"
    "theorem-library/holomorphic-basics-2"
    "theorem-library/cc-reciprocal"
    "structure-library/interval-calculus"
    "structure-library/regulated-primitive"
    "theorem-library/interval-calculus-laws"
    "theorem-library/interval-mvt"
    "structure-library/interval-extremum"
    "theorem-library/interval-extremum"
    "structure-library/one-sided-derivative"
    "theorem-library/one-sided-derivative-laws"
    "structure-library/interval-taylor"
    "theorem-library/directional-derivative"
    "theorem-library/nvs-taylor-proof"
    "theorem-library/antiderivative"
    "theorem-library/antiderivative-transfer"
    "theorem-library/antiderivative-lipschitz"
    "theorem-library/witness-family-choice"
    "theorem-library/antiderivative-normalize"
    "theorem-library/antiderivable-uniform-limit"
    "theorem-library/series-antiderivable"
    "theorem-library/c-int"
    "theorem-library/c-int-oriented"
    "theorem-library/bernstein-ccint"
    "theorem-library/rake-bolzano-weierstrass"
    "theorem-library/rake-bolzano-weierstrass-2"
    "theorem-library/rake-ascoli-diagonal"
    "theorem-library/bernstein-antiderivable"
    "theorem-library/antiderivable-affine-subst"
    "theorem-library/continuous-antiderivable"
    "theorem-library/c-int-change-of-variable"
    "theorem-library/log"
    "theorem-library/r-exp"
    "theorem-library/rpow-star"
    "theorem-library/rpow-star-convexity"
    "structure-library/functor-invariance"
    "theorem-library/metric-top-proof"
    "theorem-library/metric-top-functorial-proof"
    "theorem-library/rake-bdd-metric"
    "theorem-library/metrizable-compact-image"
    "theorem-library/metrizable-bounded-proof"
    "theorem-library/geometric-series"
    "theorem-library/limsup-tests"
    "theorem-library/rpow-defined"
    "theorem-library/rake-asm-b1"
    "theorem-library/ps-series-bridges"
    "theorem-library/ratio-test-proof"
    "theorem-library/rake-series"
    "theorem-library/rake-series2"
    "theorem-library/heine-borel-interval"
    "theorem-library/cc-coords-laws"
    "theorem-library/product2-cc"
    "structure-library/path-integral"
    "structure-library/segments-triangles"
    "structure-library/road-juxtaposition"
    "theorem-library/regulated-primitive-laws"
    "theorem-library/regulated-step-approx"
    "theorem-library/has-deriv-at-more"
    "theorem-library/has-deriv-at-chain"
    "theorem-library/interval-taylor"
    "theorem-library/zero-deriv-off-countable"
    "theorem-library/pw-antiderivative-laws"
    "theorem-library/cc-int-laws"
    "theorem-library/road-laws"
    "theorem-library/pw-int-laws-2"
    "theorem-library/taylor-cluster"
    "theorem-library/frechet-metric"
    "theorem-library/frechet-open-mapping-proof"
    "theorem-library/frechet-banach-steinhaus"
    "theorem-library/rake-asm-1"
    "theorem-library/rake-asm-b2"
    "theorem-library/rake-asm-b5"
    "theorem-library/primitive-glue"
    "theorem-library/pw-int-laws-3"
    "theorem-library/primitive-uniform-limit"
    "structure-library/rn-vocab"
    "theorem-library/calc2-rn-basics"
    "theorem-library/calc2-rn-norm"
    "theorem-library/calc2-rn-nvs"
    "theorem-library/calc2-segment"
    "theorem-library/calc2-dirderiv"
    "theorem-library/calc2-prop229"
    "theorem-library/calc2-prop228"
    "structure-library/hilbert-space"
    "theorem-library/hilbert-projection"
    "structure-library/sip-vocab"
    "theorem-library/sip-a"
    "structure-library/sip-complex-vocab"
    "theorem-library/sip-b"
    "structure-library/sip-hilbert-vocab"
    "theorem-library/sip-d1"
    "theorem-library/rake-asm-b3"
    "theorem-library/series-domination"
    "theorem-library/regulated-has-primitive"
    "theorem-library/road-laws-2"
    "theorem-library/compact-image"
    "structure-library/calc3-vocab"
    "theorem-library/calc3-closed"
    "theorem-library/calc3-compact-closed"
    "theorem-library/calc3-uniform"
    "theorem-library/calc3-extension"
    "theorem-library/pw-int-order"
  
    "structure-library/extended-reals-updown"   ; wave 2026-10-26/27
    "theorem-library/extinf-points"   ; wave 2026-10-26/27
    "theorem-library/rr-star-order-thms"   ; wave 2026-10-26/27
    "theorem-library/extinf-semigroups"   ; wave 2026-10-26/27
    "theorem-library/rabasics-trunc"   ; wave 2026-10-26/27
    "theorem-library/rabasics-open"   ; wave 2026-10-26/27
    "theorem-library/rabasics-closed"   ; wave 2026-10-26/27
    "theorem-library/ms-compose-continuous"   ; wave 2026-10-26/27
    "theorem-library/rabasics-monotone"   ; wave 2026-10-26/27
    "theorem-library/rabasics-extline"   ; wave 2026-10-26/27
    "theorem-library/rabasics-extline2"   ; wave 2026-10-26/27
    "theorem-library/extinf-iso"   ; wave 2026-10-26/27
    "theorem-library/extorder-iso"   ; wave 2026-10-26/27
    "structure-library/rb2-vocab"   ; wave 2026-10-26/27
    "theorem-library/rb2-dir"   ; wave 2026-10-26/27
    "structure-library/ca51-vocab"   ; wave 2026-10-26/27
    "theorem-library/ca51-compact-laws"   ; wave 2026-10-26/27
    "theorem-library/ca51-exhaustion"   ; wave 2026-10-26/27
    "theorem-library/qq-countable"   ; wave 2026-10-26/27
    "structure-library/mb12-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb12-snow"   ; wave 2026-10-26/27
    "theorem-library/mb12-seq"   ; wave 2026-10-26/27
    "theorem-library/mb12-ultra"   ; wave 2026-10-26/27
    "structure-library/isom-vocab"   ; wave 2026-10-26/27
    "theorem-library/isom-uc"   ; wave 2026-10-26/27
    "theorem-library/isom-equicont"   ; wave 2026-10-26/27
    "theorem-library/isom-supdist"   ; wave 2026-10-26/27
    "theorem-library/isom-dense"   ; wave 2026-10-26/27
    "theorem-library/isom-group"   ; wave 2026-10-26/27
    "structure-library/isom2-vocab"   ; wave 2026-10-26/27
    "structure-library/isom2-rrvs-vocab"   ; wave 2026-10-26/27
    "theorem-library/isom2-group"   ; wave 2026-10-26/27
    "theorem-library/mg-struct"   ; wave 2026-10-26/27
    "theorem-library/isom2-dense"   ; wave 2026-10-26/27
    "theorem-library/isom2-rrfield"   ; wave 2026-10-26/27
    "theorem-library/isom2-rrvs"   ; wave 2026-10-26/27
    "theorem-library/mb12b-finsum"   ; wave 2026-10-26/27
    "theorem-library/mb12b-dim"   ; wave 2026-10-26/27
    "theorem-library/dual-space-readoffs"   ; wave 2026-10-26/27
    "theorem-library/dual-nvs"   ; wave 2026-10-26/27
    "structure-library/bidual"   ; wave 2026-10-26/27
    "theorem-library/tvs-bidual"   ; wave 2026-10-26/27
    "theorem-library/norm-attained-general"   ; wave 2026-10-26/27
    "structure-library/minkowski-functional"   ; wave 2026-10-26/27
    "theorem-library/tvs-minkowski"   ; wave 2026-10-26/27
    "structure-library/seminorm-extension"   ; wave 2026-10-26/27
    "theorem-library/tvs-seminorm-extension"   ; wave 2026-10-26/27
    "structure-library/tvs-vocab"   ; wave 2026-10-26/27
    "theorem-library/tvs-seminorm-top"   ; wave 2026-10-26/27
    "theorem-library/tvs-seminorm-tvs"   ; wave 2026-10-26/27
    "theorem-library/tvs-rn"   ; wave 2026-10-26/27
    "theorem-library/tvs-continuity"   ; wave 2026-10-26/27
    "theorem-library/tvs-functional"   ; wave 2026-10-26/27
    "theorem-library/tvs-extremal"   ; wave 2026-10-26/27
    "theorem-library/tvs-hyperplane"   ; wave 2026-10-26/27
    "structure-library/convex-functional"   ; wave 2026-10-26/27
    "theorem-library/tvs-hahn-banach-convex"   ; wave 2026-10-26/27
    "structure-library/top-closed"   ; wave 2026-10-26/27
    "theorem-library/tvs-kernel-closed"   ; wave 2026-10-26/27
    "structure-library/line-coefficient"   ; wave 2026-10-26/27
    "theorem-library/tvs-geometric-hb"   ; wave 2026-10-26/27
    "structure-library/tvs-product-line"   ; wave 2026-10-26/27
    "theorem-library/tvs-product-line"   ; wave 2026-10-26/27
    "structure-library/nets"   ; wave 2026-10-26/27
    "theorem-library/nets"   ; wave 2026-10-26/27
    "structure-library/top-product"   ; wave 2026-10-26/27
    "theorem-library/top-product"   ; wave 2026-10-26/27
    "structure-library/weak-star"   ; wave 2026-10-26/27
    "theorem-library/tvs-alaoglu"   ; wave 2026-10-26/27
    "structure-library/weak-star-separable"   ; wave 2026-10-26/27
    "theorem-library/tvs-alaoglu-separable"   ; wave 2026-10-26/27
    "structure-library/tb11-vocab"   ; wave 2026-10-26/27
    "theorem-library/tb11-a5"   ; wave 2026-10-26/27
    "structure-library/tg-vocab"   ; wave 2026-10-26/27
    "theorem-library/tg-struct"   ; wave 2026-10-26/27
    "theorem-library/top-groups"   ; wave 2026-10-26/27
    "structure-library/cg1-vocab"   ; wave 2026-10-26/27
    "theorem-library/cg1-basic"   ; wave 2026-10-26/27
    "theorem-library/cg1-conn"   ; wave 2026-10-26/27
    "theorem-library/cg1-group"   ; wave 2026-10-26/27
    "theorem-library/cg2-top"   ; wave 2026-10-26/27
    "theorem-library/cg2-compact"   ; wave 2026-10-26/27
    "theorem-library/cvx-tb"   ; wave 2026-10-26/27
    "structure-library/cg4-vocab"   ; wave 2026-10-26/27
    "theorem-library/cg4-cosets"   ; wave 2026-10-26/27
    "theorem-library/cg4-opg"   ; wave 2026-10-26/27
    "theorem-library/cg4-seg"   ; wave 2026-10-26/27
    "theorem-library/cg4-rep"   ; wave 2026-10-26/27
    "theorem-library/cg4-hom"   ; wave 2026-10-26/27
    "theorem-library/cg4-ext"   ; wave 2026-10-26/27
    "theorem-library/cg4-local"   ; wave 2026-10-26/27
    "theorem-library/catools-evt"   ; wave 2026-10-26/27
    "theorem-library/product2-compact"   ; wave 2026-10-26/27
    "theorem-library/inclusion-exclusion"   ; wave 2026-10-26/27
    "theorem-library/euler-phi-product"   ; wave 2026-10-26/27
    "theorem-library/phi-growth"   ; wave 2026-10-26/27
    "theorem-library/group-orders"   ; wave 2026-10-26/27
    "structure-library/ccr1-vocab"   ; wave 2026-10-26/27
    "theorem-library/ccr1-ultrametric"   ; wave 2026-10-26/27
    "structure-library/ccr2-vocab"   ; wave 2026-10-26/27
    "structure-library/ccr3-vocab"   ; wave 2026-10-26/27
    "theorem-library/ccr2-nv"   ; wave 2026-10-26/27
    
    "theorem-library/regulated-on-glue"   ; wave-2 2026-10-30
    "theorem-library/rps-lt-le-trans"   ; wave-2 2026-10-30
    "theorem-library/rr-lt-pos-inf"   ; wave-2 2026-10-30
    "theorem-library/cc-exhaust-radius-decrease"   ; wave-2 2026-10-30
    "theorem-library/sip-quotient-complete"   ; wave-2 2026-10-30
    "theorem-library/calint-regulated-step"   ; wave-2 2026-10-30
    "structure-library/calint-vocab"   ; wave-2 2026-10-30
    "theorem-library/calint-deriv-limit"   ; wave-2 2026-10-30
    "theorem-library/real-riesz"   ; wave-2 2026-10-30
    "structure-library/nvlocal-vocab"   ; wave-2 2026-10-30
    
    "theorem-library/cc-magnitude-zero"   ; wave 2026-11-09/10
    "theorem-library/ba-metric-lemmas"   ; wave 2026-11-09/10
    "theorem-library/fekete"   ; wave 2026-11-09/10
    "theorem-library/cc-norming-functional"   ; wave 2026-11-09/10
    "theorem-library/cc-product"   ; wave 2026-11-09/10
    "theorem-library/complete-criterion"   ; wave 2026-11-09/10
    "theorem-library/cc-top-continuity"   ; wave 2026-11-09/10
    "theorem-library/top-power-compact"   ; wave 2026-11-09/10
    "theorem-library/ba1i-dominated"   ; wave 2026-11-09/10
    "theorem-library/cc-real-part-facts"   ; wave 2026-11-09/10
    "theorem-library/cc-magnitude-sq"   ; wave 2026-11-09/10
    "theorem-library/cc-im-i-mul"   ; wave 2026-11-09/10
    "theorem-library/cc-real-bound"   ; wave 2026-11-09/10
    "theorem-library/cc-magnitude-i"   ; wave 2026-11-09/10
    "theorem-library/rr-square-facts"   ; wave 2026-11-09/10
    "theorem-library/limit-frequent"   ; wave 2026-11-09/10
    "structure-library/basw-vocab"   ; wave 2026-11-09/10
    "structure-library/km-vocab"   ; wave 2026-11-09/10
    "theorem-library/krein-milman"   ; wave 2026-11-09/10
    "structure-library/hilbert-onb-vocab"   ; wave 2026-11-09/10
    "theorem-library/hilbert-onb"   ; wave 2026-11-09/10
    "theorem-library/abs-summable-cn"   ; wave 2026-11-09/10
    "structure-library/l2-families-vocab"   ; wave 2026-11-09/10
    "theorem-library/l2-families"   ; wave 2026-11-09/10
    "theorem-library/rps-finsum-mono-set"   ; wave 2026-11-09/10
    "theorem-library/complete-transfer"   ; wave 2026-11-09/10
    "theorem-library/rps-finsum-le-ptwise"   ; wave 2026-11-09/10
    "theorem-library/etimes-real-in"   ; wave 2026-11-09/10
    "theorem-library/countable-products"   ; wave 2026-11-09/10
    "theorem-library/countable-fin-subsets"   ; wave 2026-11-09/10
    "theorem-library/tvs-single-bound"   ; wave 2026-11-09/10
    "theorem-library/basw3-nag"   ; wave 2026-11-09/10
    "structure-library/cnvs-vocab"   ; wave 2026-11-09/10
    "theorem-library/cnvs-a"   ; wave 2026-11-09/10
    "theorem-library/cnvs-b"   ; wave 2026-11-09/10
    "theorem-library/cnvs-c"   ; wave 2026-11-09/10
    "structure-library/cnvs-comp-vocab"   ; wave 2026-11-09/10
    "theorem-library/cnvs-d"   ; wave 2026-11-09/10
    "theorem-library/cnvs-comp"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-metric"   ; wave 2026-11-09/10
    "structure-library/ccr1109a2-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-nv"   ; wave 2026-11-09/10
    "structure-library/ccr1109a3-laurent-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-laurent"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a3-laurent-ring"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a3-laurent-val"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a3-laurent-field"   ; wave 2026-11-09/10
    "structure-library/ccr1109a4-laurent-lim-vocab"   ; wave 2026-11-09/10
    "structure-library/ccr1109a5-vocab"   ; wave 2026-11-09/10
    "structure-library/ccr-ch3-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3-ops"   ; wave 2026-11-09/10
    "structure-library/ccr-ch3b-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3b-alg"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3b-an"   ; wave 2026-11-09/10
    "structure-library/ccr-ch3c-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3c-det"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3c-ball"   ; wave 2026-11-09/10
    "theorem-library/rr-nonneg-below-all-zero"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3c-pb"   ; wave 2026-11-09/10
    "structure-library/ccr4x-ext-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr4x-ext"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3c-ext"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3d-ultra"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3d-fam"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3d-ext"   ; wave 2026-11-09/10
    "theorem-library/ccr-ch3e-norms"   ; wave 2026-11-09/10
    "structure-library/ccr4x-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr4x-eisen"   ; wave 2026-11-09/10
    "theorem-library/ccr4x-zpow"   ; wave 2026-11-09/10
    "theorem-library/ccr4x-series"   ; wave 2026-11-09/10
    "theorem-library/ccr4x-unique"   ; wave 2026-11-09/10
    "structure-library/ccr4b-vocab"   ; wave 2026-11-09/10
    "theorem-library/compact-inter-closed"   ; wave 2026-11-09/10
    "structure-library/ccr4c-subnf-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr4c-subnf"   ; wave 2026-11-09/10
    "theorem-library/aif-scale-small"   ; wave 2026-11-09/10
    "theorem-library/ccr4d-converge"   ; wave 2026-11-09/10
    "structure-library/ccr4d-ext-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr4d-ext"   ; wave 2026-11-09/10
    "theorem-library/ccr-kn-norms"   ; wave 2026-11-09/10
    "structure-library/hc-vocab"   ; wave 2026-11-09/10
    "theorem-library/esup-lt-witness"   ; wave 2026-11-09/10
    "theorem-library/haar-fixed-point"   ; wave 2026-11-09/10
    "structure-library/hc2-vocab"   ; wave 2026-11-09/10
    "theorem-library/haar-c2"   ; wave 2026-11-09/10
    "structure-library/hc3-vocab"   ; wave 2026-11-09/10
    "theorem-library/haar-c3"   ; wave 2026-11-09/10
    "theorem-library/tvs-sub-bound"   ; wave 2026-11-11
    ))

(library complex-analysis
  (title "Complex Analysis")
  (about "Holomorphic functions and power series over CC; the exponential and the logarithm; line integrals, Goursat and the Cauchy integral formula; winding numbers; Cauchy's estimates, Liouville and the fundamental theorem of algebra; Morera; the Gamma function.")
  (imports analysis)
  (files
    "theorem-library/cc-series"
    "theorem-library/cc-diff-laws-2"
    "structure-library/cc-power-series"
    "theorem-library/cc-power-series-laws"
    "theorem-library/cc-power-series-deriv"
    "theorem-library/cps-taylor-coefficients"
    "theorem-library/nth-deriv-laws"
    "theorem-library/line-int-fundamental"
    "theorem-library/goursat-bricks"
    "theorem-library/regulated-algebra"
    "theorem-library/cc-int-estimate"
    "theorem-library/line-int-laws"
    "theorem-library/line-int-reparam"
    "theorem-library/goursat"
    "theorem-library/goursat-exceptional"
    "theorem-library/road-juxtaposition-laws"
    "structure-library/cc-elementary"
    "theorem-library/cc-exp"
    "structure-library/cc-pi"
    "structure-library/analytic-log"
    "theorem-library/cc-exp-kernel"
    "theorem-library/cc-exp-surjective"
    "theorem-library/analytic-log-laws"
    "theorem-library/cc-log-holomorphic"
    "structure-library/winding-number"
    "theorem-library/winding-number-laws"
    "theorem-library/analytic-from-integral"
    "theorem-library/cauchy-integral-formula"
    "theorem-library/cauchy-estimates"
    "structure-library/ca1-vocab"
    "theorem-library/ca1-matrix-rep"
    "theorem-library/ca1-alg-closed"
    "theorem-library/winding-number-integer"
    "theorem-library/winding-number-components"
    "theorem-library/cauchy-centre-mean-value"
    "theorem-library/morera"
    "structure-library/gamma-function"
    "theorem-library/gamma-function"
    "structure-library/ca5-function-spaces"
    "structure-library/ca-ac-vocab"
    "theorem-library/ca5-function-spaces"
    "theorem-library/weierstrass-convergence"
    "theorem-library/analytic-continuation"
    "theorem-library/ca5-frechet"
    "theorem-library/ca5-montel"
    "theorem-library/ca5-series"
    "theorem-library/ca6-hurwitz"
    "structure-library/ca-lft-vocab"
    "theorem-library/ca-lft-plane"
    "theorem-library/ca-lft-compose"
    "theorem-library/ca-lft-topology"
    "theorem-library/ca-lft-cayley"
    "theorem-library/ca-lft-group"
    "theorem-library/ca-lft-matrix"
    "theorem-library/ca-lft-sl2"
    "structure-library/ca-hopf-vocab"
    "theorem-library/ca-hopf-fibration"
    "theorem-library/product2-hopf"
  
    "structure-library/poly-fn-vocab"   ; wave 2026-10-26/27
    "theorem-library/poly-fn-laws"   ; wave 2026-10-26/27
    "theorem-library/poly-fn-roots"   ; wave 2026-10-26/27
    "theorem-library/poly-fn-weierstrass"   ; wave 2026-10-26/27
    "theorem-library/poly-fn-holomorphic"   ; wave 2026-10-26/27
    "theorem-library/ca-log-disc"   ; wave 2026-10-26/27
    "theorem-library/ca-connected"   ; wave 2026-10-26/27
    "theorem-library/ca-montel-compact"   ; wave 2026-10-26/27
    "theorem-library/rb2-path"   ; wave 2026-10-26/27
    "theorem-library/ca51-cc"   ; wave 2026-10-26/27
    "structure-library/ch3a-vocab"   ; wave 2026-10-26/27
    "theorem-library/ch3a-maxmod"   ; wave 2026-10-26/27
    "theorem-library/ch3a-estimates"   ; wave 2026-10-26/27
    "theorem-library/ch3a-schwarz"   ; wave 2026-10-26/27
    "theorem-library/ch3a-growth"   ; wave 2026-10-26/27
    "theorem-library/ch3a-factor"   ; wave 2026-10-26/27
    "theorem-library/ch3b-const"   ; wave 2026-10-26/27
    "theorem-library/ch3b-log"   ; wave 2026-10-26/27
    "theorem-library/catools-nthlocal"   ; wave 2026-10-26/27
    "theorem-library/catools-hfrechet"   ; wave 2026-10-26/27
    "theorem-library/compact-margins"   ; wave 2026-10-26/27
    "structure-library/ca-homotopy-vocab"   ; wave 2026-10-26/27
    "theorem-library/good-approx"   ; wave 2026-10-26/27
    "theorem-library/poly-road"   ; wave 2026-10-26/27
    "theorem-library/homotopy"   ; wave 2026-10-26/27
    "theorem-library/sc-primitive"   ; wave 2026-10-26/27
    "theorem-library/sc-log-roots"   ; wave 2026-10-26/27
    "theorem-library/riemann-reduction"   ; wave 2026-10-26/27
    "structure-library/algnum-vocab"   ; wave 2026-10-26/27
    "theorem-library/algnum-countable"   ; wave 2026-10-26/27
    "theorem-library/algebraic-numbers"   ; wave 2026-10-26/27
    "structure-library/ccr4-vocab"   ; wave 2026-10-26/27
    "theorem-library/ccr4-chars"   ; wave 2026-10-26/27
    "structure-library/padic-vocab"   ; wave 2026-10-26/27
    "theorem-library/padic-laws"   ; wave 2026-10-26/27
    
    "structure-library/ca-angle-vocab"   ; wave-2 2026-10-30
    "structure-library/ca-line-vocab"   ; wave-2 2026-10-30
    "theorem-library/removable-singularities"   ; wave-2 2026-10-30
    "theorem-library/power-series-coef-bound"   ; wave-2 2026-10-30
    "theorem-library/principal-part"   ; wave-2 2026-10-30
    "theorem-library/triangle-orientation"   ; wave-2 2026-10-30
    "theorem-library/triangle-winding"   ; wave-2 2026-10-30
    "theorem-library/triangle-cauchy-formula"   ; wave-2 2026-10-30
    "theorem-library/holomorphy-across-line"   ; wave-2 2026-10-30
    "theorem-library/schwarz-reflection"   ; wave-2 2026-10-30
    "structure-library/gamma-continuation-vocab"   ; wave-2 2026-10-30
    "theorem-library/gamma-continuation"   ; wave-2 2026-10-30
    "theorem-library/calint-poly-integral"   ; wave-2 2026-10-30
    "structure-library/mvp-vocab"   ; wave-2 2026-10-30
    "theorem-library/mvp-max"   ; wave-2 2026-10-30
    "theorem-library/mvp-modulus"   ; wave-2 2026-10-30
    "theorem-library/mvp-bounded"   ; wave-2 2026-10-30
    "theorem-library/mvp-holo"   ; wave-2 2026-10-30
    "structure-library/ch4a-vocab"   ; wave-2 2026-10-30
    "theorem-library/ch4a-laurent"   ; wave-2 2026-10-30
    "theorem-library/ch4a-straight"   ; wave-2 2026-10-30
    "theorem-library/ch4a-annulus"   ; wave-2 2026-10-30
    "theorem-library/ch4a-termwise"   ; wave-2 2026-10-30
    "theorem-library/ch4a-outer"   ; wave-2 2026-10-30
    "theorem-library/ch4a-circle"   ; wave-2 2026-10-30
    "theorem-library/ch4a-coef"   ; wave-2 2026-10-30
    "theorem-library/ch4a-expansion"   ; wave-2 2026-10-30
    "theorem-library/ch4a-punctured"   ; wave-2 2026-10-30
    "theorem-library/ch4a-coefcont"   ; wave-2 2026-10-30
    "structure-library/zero-order-vocab"   ; wave-2 2026-10-30
    "theorem-library/zero-order-laws"   ; wave-2 2026-10-30
    "structure-library/ch4b-vocab"   ; wave-2 2026-10-30
    "theorem-library/ch4b-residues"   ; wave-2 2026-10-30
    "theorem-library/ch4b-mero"   ; wave-2 2026-10-30
    "theorem-library/ch4c-inverse"   ; wave-2 2026-10-30
    "structure-library/ch4d-vocab"   ; wave-2 2026-10-30
    "theorem-library/ch4d-meromorphic"   ; wave-2 2026-10-30
    "structure-library/infinite-products-vocab"   ; wave-2 2026-10-30
    "theorem-library/ch6-prod"   ; wave-2 2026-10-30
    "theorem-library/ch6-fun"   ; wave-2 2026-10-30
    "theorem-library/ch6-weier"   ; wave-2 2026-10-30
    "theorem-library/ch6-mult"   ; wave-2 2026-10-30
    "theorem-library/ch6-quot"   ; wave-2 2026-10-30
    "theorem-library/ch6-gamma"   ; wave-2 2026-10-30
    "theorem-library/ch6-euler"   ; wave-2 2026-10-30
    "theorem-library/ch6-pole"   ; wave-2 2026-10-30
    "theorem-library/ch6-g629"   ; wave-2 2026-10-30
    "theorem-library/ch6-g361"   ; wave-2 2026-10-30
    "structure-library/qp-vocab"   ; wave-2 2026-10-30
    "theorem-library/qp-laws"   ; wave-2 2026-10-30
    "structure-library/pruefer-vocab"   ; wave-2 2026-10-30
    "theorem-library/pruefer-laws"   ; wave-2 2026-10-30
    
    "theorem-library/ccr1109a-late"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a-nv"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-val"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a2-res"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a4-laurent-complete"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a5-finite-field"   ; wave 2026-11-09/10
    "structure-library/ccr5-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr5-dual"   ; wave 2026-11-09/10
    "theorem-library/ccr5-selfdual"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a5-pairing"   ; wave 2026-11-09/10
    "structure-library/ccr1109a6-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a6-chars"   ; wave 2026-11-09/10
    "theorem-library/ccr1109a6-laurent"   ; wave 2026-11-09/10
    "theorem-library/ccr4b-base"   ; wave 2026-11-09/10
    "theorem-library/ccr4b-remark418"   ; wave 2026-11-09/10
    "theorem-library/ccr4c-local"   ; wave 2026-11-09/10
    "structure-library/ccr6e-vocab"   ; wave 2026-11-09/10
    "theorem-library/ccr6-e"   ; wave 2026-11-09/10
    "theorem-library/ccr6-f"   ; wave 2026-11-09/10
    "theorem-library/ccr-adj-integral"   ; wave 2026-11-09/10
    "theorem-library/ccr6-g"   ; wave 2026-11-09/10
    "theorem-library/ccr6-h"   ; wave 2026-11-09/10
    "theorem-library/ccr4e-unif0"   ; wave 2026-11-11
    "structure-library/ccr4f-vocab"   ; wave 2026-11-11
    "theorem-library/ccr4f-digits"   ; wave 2026-11-11
    "theorem-library/ccr4f-poly"   ; wave 2026-11-11
    "theorem-library/ccr4g-coords"   ; wave 2026-11-11
    "theorem-library/ccr4g-residue"   ; wave 2026-11-11
    ))

(library measure
  (title "Measure")
  (about "Sigma-algebras, outer measures and the Caratheodory construction; measures and measurable maps; the integral of simple and measurable functions; sums over the extended nonnegative reals.")
  (imports analysis)
  (files
    "theorem-library/mb12-metric"   ; wave 2026-10-26/27 (measure: it states SET-DIST)
    "structure-library/sigma-algebra"
    "structure-library/measure"
    "structure-library/measurable-space"
    "structure-library/integral"
    "structure-library/simple-integral"
    "theorem-library/rake-measure"
    "theorem-library/rake-measure2"
    "theorem-library/measure-laws"
    "theorem-library/integral-laws"
    "theorem-library/esum-scale"
    "theorem-library/integral-convergence"
    "theorem-library/caratheodory"
    "structure-library/outer-measure-construction"
    "theorem-library/outer-measure-construction"
    "structure-library/real-integral"
    "theorem-library/real-integral"
    "structure-library/monotone-class"
    "theorem-library/monotone-class"
    "theorem-library/lebesgue-interval-length"
    "structure-library/metric-outer-measure"
    "theorem-library/metric-outer-measure"
    "theorem-library/riesz-markov-cantor"
    "theorem-library/positive-extension"
    "theorem-library/lebesgue-measure-line"
    "structure-library/lebesgue-translate"
    "theorem-library/lebesgue-measure-unique"
    "theorem-library/lebesgue-translation-invariant"
    "structure-library/lp-inequalities"
    "theorem-library/lp-inequalities"
    "structure-library/lp-seminorm"
    "theorem-library/lp-seminorm"
    "structure-library/product-measure"
    "theorem-library/product-measure"
    "theorem-library/esup-product"
    "structure-library/sip-l2-vocab"
    "theorem-library/sip-c"
    "structure-library/push-forward"
    "theorem-library/push-forward"
    "theorem-library/riesz-markov"
    "theorem-library/riesz-markov-compact"
  
    "structure-library/hausdorff-vocab"   ; wave 2026-10-26/27
    "theorem-library/method-ii"   ; wave 2026-10-26/27
    "theorem-library/hausdorff-measure"   ; wave 2026-10-26/27
    "theorem-library/hausdorff-dimension"   ; wave 2026-10-26/27
    "theorem-library/hausdorff-restrict"   ; wave 2026-10-26/27
    "structure-library/mb-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb-conull"   ; wave 2026-10-26/27
    "theorem-library/mb-complete"   ; wave 2026-10-26/27
    "theorem-library/mb-completion"   ; wave 2026-10-26/27
    "theorem-library/mb-restrict"   ; wave 2026-10-26/27
    "theorem-library/mb-outer"   ; wave 2026-10-26/27
    "structure-library/mb4-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb4-borel-subspace"   ; wave 2026-10-26/27
    "theorem-library/mb4-borel-product"   ; wave 2026-10-26/27
    "theorem-library/mb4-sieve"   ; wave 2026-10-26/27
    "theorem-library/mb4-polish-open"   ; wave 2026-10-26/27
    "theorem-library/mb4-sigma-finite"   ; wave 2026-10-26/27
    "theorem-library/mb4-separable-measure"   ; wave 2026-10-26/27
    "structure-library/mb35-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb35-regular"   ; wave 2026-10-26/27
    "structure-library/mb35-souslin-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb35-souslin"   ; wave 2026-10-26/27
    "structure-library/measure-ch1-vocab"   ; wave 2026-10-26/27
    "theorem-library/measure-ch1-algebras"   ; wave 2026-10-26/27
    "theorem-library/measure-ch1-pullback"   ; wave 2026-10-26/27
    "theorem-library/measure-ch1-vitali"   ; wave 2026-10-26/27
    "theorem-library/measure-ch1-vitali-q"   ; wave 2026-10-26/27
    "structure-library/mb67-vocab"   ; wave 2026-10-26/27
    "theorem-library/mb67-baire"   ; wave 2026-10-26/27
    "theorem-library/mb67-souslin"   ; wave 2026-10-26/27
    "theorem-library/mb67-lusin"   ; wave 2026-10-26/27
    "theorem-library/mb67-standard"   ; wave 2026-10-26/27
    "theorem-library/mb67-prod2"   ; wave 2026-10-26/27
    "theorem-library/mb67-prod"   ; wave 2026-10-26/27
    "theorem-library/mb67-sum"   ; wave 2026-10-26/27
    "theorem-library/mb67-lusin2"   ; wave 2026-10-26/27
    "theorem-library/mb67-sep"   ; wave 2026-10-26/27
    "theorem-library/mb67-ls"   ; wave 2026-10-26/27
    "theorem-library/mb67-s38"   ; wave 2026-10-26/27
    "theorem-library/mb67-b32"   ; wave 2026-10-26/27
    "theorem-library/mb67-s35"   ; wave 2026-10-26/27
    
    "structure-library/measure-step"   ; wave-2 2026-10-30
    "theorem-library/integral-unique"   ; wave-2 2026-10-30
    "theorem-library/lp-convergence"   ; wave-2 2026-10-30
    "theorem-library/lp-step-dense"   ; wave-2 2026-10-30
    "theorem-library/lp-measure-isomorphism"   ; wave-2 2026-10-30
    "theorem-library/lp-complete"   ; wave-2 2026-10-30
    "theorem-library/l2-hilbert"   ; wave-2 2026-10-30
    "theorem-library/radon-nikodym"   ; wave-2 2026-10-30
    "structure-library/l1-dual"   ; wave-2 2026-10-30
    "theorem-library/l1-dual"   ; wave-2 2026-10-30
    "structure-library/signed-measure"   ; wave-2 2026-10-30
    "theorem-library/signed-measure-ext"   ; wave-2 2026-10-30
    "theorem-library/signed-measure-laws"   ; wave-2 2026-10-30
    "theorem-library/jordan-decomposition"   ; wave-2 2026-10-30
    "structure-library/complex-measure"   ; wave-2 2026-10-30
    "theorem-library/complex-measure-laws"   ; wave-2 2026-10-30
    "theorem-library/complex-measure-polar"   ; wave-2 2026-10-30
    "structure-library/step-maps"   ; wave-2 2026-10-30
    "theorem-library/measurable-maps-metric"   ; wave-2 2026-10-30
    "structure-library/local-measure"   ; wave-2 2026-10-30
    "theorem-library/local-measure"   ; wave-2 2026-10-30
    "structure-library/doubling-functions"   ; wave-2 2026-10-30
    "theorem-library/doubling-functions"   ; wave-2 2026-10-30
    
    "theorem-library/esum-tonelli"   ; wave 2026-11-09/10
    "theorem-library/esum-tail"   ; wave 2026-11-09/10
    "theorem-library/esum-cartesian"   ; wave 2026-11-09/10
    "structure-library/l2c-vocab"   ; wave 2026-11-09/10
    "theorem-library/l2c-a"   ; wave 2026-11-09/10
    "theorem-library/l2c-b"   ; wave 2026-11-09/10
    "theorem-library/l2c-c"   ; wave 2026-11-09/10
    "theorem-library/l2-bridge"   ; wave 2026-11-09/10
    "theorem-library/signed-fubini"   ; wave 2026-11-09/10
    "theorem-library/l2-kernel-sections"   ; wave 2026-11-09/10
    "theorem-library/l2-kernel-measurable"   ; wave 2026-11-09/10
    "theorem-library/l2-kernel-operator"   ; wave 2026-11-09/10
    "structure-library/l2-integral-operator"   ; wave 2026-11-09/10
    "theorem-library/kernel-apply"   ; wave 2026-11-09/10
    "theorem-library/cl2-integral-operator"   ; wave 2026-11-09/10
    ))

(library operator-algebras
  (title "Operator Algebras")
  (about "Banach and C*-algebras, the Gelfand theory, bounded and unbounded operators on Hilbert space, operator topologies, compact and Hilbert-Schmidt operators (the user's BanachAlgebras notes, chapters 1-6; added 2026-11-10).")
  (imports complex-analysis measure)
  (files
  
    "structure-library/ba-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-subtype-laws"   ; wave 2026-11-09/10
    "structure-library/ba-cx-vocab"   ; wave 2026-11-09/10
    "structure-library/ba-neumann-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-laws"   ; wave 2026-11-09/10
    "theorem-library/ba-elem"   ; wave 2026-11-09/10
    "theorem-library/ba-neumann"   ; wave 2026-11-09/10
    "theorem-library/ba-spectrum"   ; wave 2026-11-09/10
    "theorem-library/ba-inverse"   ; wave 2026-11-09/10
    "theorem-library/ba-ideal-closure"   ; wave 2026-11-09/10
    "theorem-library/ba-resolvent"   ; wave 2026-11-09/10
    "theorem-library/ba-gelfand-mazur"   ; wave 2026-11-09/10
    "theorem-library/ba-gelfand"   ; wave 2026-11-09/10
    "theorem-library/ba-fekete"   ; wave 2026-11-09/10
    "theorem-library/ba-unitization"   ; wave 2026-11-09/10
    "structure-library/ba-quotient-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-quotient"   ; wave 2026-11-09/10
    "theorem-library/ba-spectrum-nonempty"   ; wave 2026-11-09/10
    "theorem-library/ba-gelfand-continuous"   ; wave 2026-11-09/10
    "theorem-library/ba-maximal-ideal"   ; wave 2026-11-09/10
    "structure-library/ba-quotient-na-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-quotient-na"   ; wave 2026-11-09/10
    "theorem-library/ba-spectral-radius"   ; wave 2026-11-09/10
    "theorem-library/ba-gelfand-compact"   ; wave 2026-11-09/10
    "theorem-library/ba-characters"   ; wave 2026-11-09/10
    "theorem-library/ba-gelfand-formula"   ; wave 2026-11-09/10
    "theorem-library/ba-cstar-laws"   ; wave 2026-11-09/10
    "theorem-library/kal-laws"   ; wave 2026-11-09/10
    "theorem-library/kal-unit"   ; wave 2026-11-09/10
    "theorem-library/kal-unit-cna"   ; wave 2026-11-09/10
    "theorem-library/ba1i-unit-banach"   ; wave 2026-11-09/10
    "theorem-library/ba1i-unit-star"   ; wave 2026-11-09/10
    "structure-library/ba2-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba2-cstar"   ; wave 2026-11-09/10
    "theorem-library/ba2b-radius"   ; wave 2026-11-09/10
    "theorem-library/ba2b-hom"   ; wave 2026-11-09/10
    "structure-library/ba2b-gen-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba2b-gen"   ; wave 2026-11-09/10
    "theorem-library/basw-top"   ; wave 2026-11-09/10
    "structure-library/basw2-vocab"   ; wave 2026-11-09/10
    "theorem-library/basw2-cx"   ; wave 2026-11-09/10
    "theorem-library/ba2b-gelfand"   ; wave 2026-11-09/10
    "theorem-library/ba2b-unique"   ; wave 2026-11-09/10
    "theorem-library/kal-cstar-122"   ; wave 2026-11-09/10
    "structure-library/ba-ops-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-bh"   ; wave 2026-11-09/10
    "structure-library/ba-bh2-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-bh2"   ; wave 2026-11-09/10
    "structure-library/ba-unbdd-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-g1"   ; wave 2026-11-09/10
    "theorem-library/ba-g2"   ; wave 2026-11-09/10
    "theorem-library/hilbert-separable"   ; wave 2026-11-09/10
    "theorem-library/sums-to-algebra"   ; wave 2026-11-09/10
    "theorem-library/l2-families-2"   ; wave 2026-11-09/10
    "theorem-library/riesz-fischer"   ; wave 2026-11-09/10
    "theorem-library/l2-families-cips"   ; wave 2026-11-09/10
    "theorem-library/hilbert-separable-l2"   ; wave 2026-11-09/10
    "structure-library/ba-optop-vocab"   ; wave 2026-11-09/10
    "theorem-library/ba-optop"   ; wave 2026-11-09/10
    "structure-library/basw3-vocab"   ; wave 2026-11-09/10
    "theorem-library/basw3-urysohn"   ; wave 2026-11-09/10
    "theorem-library/basw4-cx"   ; wave 2026-11-09/10
    "structure-library/cnvs-ba-vocab"   ; wave 2026-11-09/10
    "theorem-library/cnvs-ba"   ; wave 2026-11-09/10
    "theorem-library/cnvs-bop-bridge"   ; wave 2026-11-09/10
    "structure-library/th3-vocab"   ; wave 2026-11-09/10
    "theorem-library/th3-vocab-unfold"   ; wave 2026-11-09/10
    "theorem-library/th3-compact"   ; wave 2026-11-09/10
    "structure-library/th3a2-vocab"   ; wave 2026-11-09/10
    "theorem-library/th3a2-compact"   ; wave 2026-11-09/10
    "theorem-library/th3a3-finrank"   ; wave 2026-11-09/10
    "theorem-library/th3a3-spectral"   ; wave 2026-11-09/10
    "theorem-library/hilbert-schmidt"   ; wave 2026-11-09/10
    "theorem-library/th3a4-spectral"   ; wave 2026-11-09/10
    "theorem-library/cc-sums-ptwise"   ; wave 2026-11-09/10
    "theorem-library/hs-inner-product"   ; wave 2026-11-09/10
    "theorem-library/hs-inner-product-2"   ; wave 2026-11-09/10
    "theorem-library/hs-inner-product-3"   ; wave 2026-11-09/10
    "theorem-library/hs-compact"   ; wave 2026-11-09/10
    "theorem-library/cl2-integral-operator-bounded"   ; wave 2026-11-09/10
    "theorem-library/th3-eigen-normalized"   ; wave 2026-11-09/10
    "theorem-library/ipf-form-plus"   ; wave 2026-11-11
    "theorem-library/ba-trace-class"   ; wave 2026-11-11
    "theorem-library/ba-graph-commutation"   ; wave 2026-11-11
    "structure-library/ba-rep-vocab"   ; wave 2026-11-11
    "structure-library/ba-gns-vocab"   ; wave 2026-11-11
    "theorem-library/ba4-sqrt"   ; wave 2026-11-11
    "theorem-library/ba4-pos"   ; wave 2026-11-11
    "theorem-library/ba4-rep"   ; wave 2026-11-11
    "theorem-library/ba4-gns"   ; wave 2026-11-11
    "theorem-library/ba4-states"   ; wave 2026-11-11
    "theorem-library/ba-optop-adjoint"   ; wave 2026-11-11
    "structure-library/ba-vn-vocab"   ; wave 2026-11-11
    "theorem-library/ba-vn"   ; wave 2026-11-11
    "structure-library/ba-amp-vocab"   ; wave 2026-11-11
    "theorem-library/ba-amp"   ; wave 2026-11-11
    "theorem-library/ba-sesq"   ; wave 2026-11-11
    "structure-library/ipf-vocab"   ; wave 2026-11-11
    "structure-library/hilbert-completion-vocab"   ; wave 2026-11-11
    "theorem-library/ipf-laws"   ; wave 2026-11-11
    "theorem-library/ipf-quotient"   ; wave 2026-11-11
    "theorem-library/hilbert-completion"   ; wave 2026-11-11
    ))

(library strand
  (title "Strand Spaces")
  (about "Messages as tokens, lists and encryptions; strands, strand spaces, nodes and the two node relations; bundles and causal precedence; origination and entry points; the adversary and the bound on what it can originate.")
  (imports core)
  (files
    "structure-library/strand-messages"
    "theorem-library/strand-messages-laws"
    "structure-library/strand-spaces"
    "theorem-library/strand-space-laws"
    "structure-library/strand-adversary"
    "theorem-library/strand-adversary-bound"
    "structure-library/nsl"
    "theorem-library/nsl"
  
    "structure-library/strand-ideals"   ; wave 2026-10-26/27
    "theorem-library/strand-ideals-laws"   ; wave 2026-10-26/27
    "structure-library/nso"   ; wave 2026-10-26/27
    "structure-library/flat-regular"   ; wave 2026-10-26/27
    "theorem-library/flat-regular-laws"   ; wave 2026-10-26/27
    "theorem-library/nso-laws"   ; wave 2026-10-26/27
    "structure-library/strand-honesty"   ; wave 2026-10-26/27
    "theorem-library/strand-honesty-laws"   ; wave 2026-10-26/27
    "structure-library/otway-rees"   ; wave 2026-10-26/27
    "theorem-library/otway-rees-laws"   ; wave 2026-10-26/27
    "theorem-library/strand-tokens-nn"   ; wave 2026-10-26/27
    "structure-library/or-missing-guarantee-instance"   ; wave 2026-10-26/27
    "theorem-library/or-missing-guarantee"   ; wave 2026-10-26/27
    ))

(library meta
  (title "The Kernel Encoded")
  (about "Expressions of the VNB language encoded as sets (syntax, free variables, substitution, rank); the core calculus as an inductively defined set DERIVABLE(T) of sequents; contextual rewriting and the rewriting rules as admissible rules of the core; the induction rules and the definedness clauses of the kernel against the core (K2, docs/meta-k2-admissibility-2026-10-08.md).")
  (imports core)
  (files
    "structure-library/meta-syntax"
    "theorem-library/meta-syntax-laws"
    "structure-library/meta-core"
    "theorem-library/meta-core-laws"
    "structure-library/meta-cr"
    "theorem-library/meta-cr-laws"
    "structure-library/meta-ind"
    "structure-library/meta-def"
    "theorem-library/meta-ind-laws"
    "theorem-library/meta-def-laws"
    "structure-library/meta-nbg"
    "theorem-library/meta-nbg-laws"
  ))

;;; files whose theorems belong to several books: each proven or asserted theorem is placed by
;;; the JOIN of the libraries of its statement's heads (libraries.scm); definitions stay with the file
(cross-cutting
  "theorem-library/rake-asm-b5"
  "theorem-library/rake-asm-1"
  "theorem-library/rake-asm-2"
  "structure-library/views"
  "theorem-library/ag-view-read-offs"
  "theorem-library/rake-setoid"
  "theorem-library/rake-analysis2"
  "theorem-library/discrete-space"
  "structure-library/subtype-laws"
  "structure-library/is-set-laws"
  "theorem-library/op-typing"
  "theorem-library/cancellation"
  "theorem-library/rake-algebra"
  "theorem-library/rake-finsum-typing"
  "theorem-library/hom-laws"
  "theorem-library/hom-kinds"
  "theorem-library/hom-functors"
  "theorem-library/hom-views"
  "theorem-library/rake-finsum-laws2"
  "theorem-library/rake-finsum-core"
  "theorem-library/rake-combinatorics"
  "theorem-library/rake-setoid2"
  "structure-library/functor-invariance"
  "structure-library/functoriality")

;;; reference pages that live in theorem-library/ and state no mathematics
(exempt
  "theorem-library/pss-topics"
  "theorem-library/reference-topics")
