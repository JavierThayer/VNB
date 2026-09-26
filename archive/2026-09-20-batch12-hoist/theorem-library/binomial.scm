;;; RETIRED 2026-09-17 (proven): bt-mul-comm -- theorem-library/rake-combinatorics.scm
;;; (that proof was in turn REMOVED 2026-09-20 as a duplicate of
;;; commutative-ring-mul-comm, theorem-library/rake-finsum-core.scm; the call
;;; sites cite that name.)
;;; binomial.scm -- the Binomial Theorem for commutative rings, over the
;;; INTEGER-RANGE sum SUM (sequences.scm), with a recursively-defined weighted
;;; coefficient COMB-KK that folds Pascal's rule into the recursion.
;;;
;;;   (x + y)^n  =  SUM(R, COMB-KK(R,x,y,n), succ n)  =  sum_{k=0}^{n} C(n,k) x^k y^(n-k)
;;;
;;; This is the IMPS-style formulation (docs/algebra.t): the index k ranges over
;;; ZZ, so k-1 is genuine integer subtraction and the coefficient vanishes for
;;; k<0 / k>m DEFINITIONALLY (comb-kk-null / comb-kk-above).  No reindex
;;; bijection, no truncated-subtraction (monus) boundary cases -- the shift is
;;; carried by the successor recurrence of SUM inside an induction (sum-expansion),
;;; exactly as IMPS's expansion-lemma.  PROVEN in binomial-proof.scm.
;;;
;;; This REPLACES the earlier FINSUM-over-ORD-SEGMENT statement, whose proof
;;; drowned in reindex-bijection + monus plumbing.  Binomial is a leaf capstone
;;; (nothing depends on it), so the representation was free to change (2026-07-04).
;;;
;;; Dependencies: sequences.scm (SUM / sum-zero / sum-succ / sum-singleton),
;;; ring-power.scm, def-by-nn-recursion (ordinals.scm).
;;; RETIRED 2026-09-14 (proven): bt-neg1-in-zz -- theorem-library/bt-shims.scm
;;; RETIRED 2026-09-14 (proven): bt-neg1-neg -- theorem-library/bt-shims.scm
;;; RETIRED 2026-09-14 (proven): bt-nn-in-zz -- theorem-library/bt-shims.scm
;;; RETIRED 2026-09-14 (proven): bt-succ-in-nn -- theorem-library/bt-shims.scm
;;; RETIRED 2026-09-14 (proven): bt-lt-succ -- theorem-library/bt-shims.scm
;;; RETIRED 2026-09-14 (proven): bt-one-in-carr -- theorem-library/ring-zero-one-power.scm

;;; -----------------------------------------------------------------------
;;; COMB-KK(R,x,y,m) : ZZ -> CARR R      k |-> C(m,k) . x^k y^(m-k)
;;;   m = 0:     k |-> IF k=0 THEN ONE(R) ELSE ZERO(R)
;;;   succ m:    k |-> x * COMB-KK(.,m)(k-1) + y * COMB-KK(.,m)(k)     [Pascal, ZZ index]
;;; Installs comb-kk-zero and comb-kk-succ (definitional == equations).
(def-by-nn-recursion 'COMB-KK '(R x y)
  '(VNB-LAMBDA k ZZ (IF (= k 0) (ONE R) (ZERO R)))
  '(m val)
  '(VNB-LAMBDA k ZZ ((ADD R) ((MUL R) x (val (- k 1))) ((MUL R) y (val k)))))

;;; -----------------------------------------------------------------------
;;; COMB-KK facts (warranted PSS supports; each is a one-step induction on m
;;; from comb-kk-zero/-succ, in the library-build spirit).
;;; -----------------------------------------------------------------------

;; The coefficient family is a total ZZ-indexed function into the carrier.
;;; comb-kk-in-fun MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.

;; Vanishing below the range: C(m,k)=0 for k<0.
;;; comb-kk-null MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.

;; Vanishing above the range: C(m,k)=0 for k>m.
;;; comb-kk-above MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.

;; The single k=0 term of the degree-0 coefficient is ONE.
;;; comb-kk-0-0 MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.

;;; -----------------------------------------------------------------------
;;; Small arithmetic / typing shims used by the induction (all warranted;
;;; each is a one-liner over ZZ/NN or a curried closure the tactic layer needs
;;; because `fact' cannot split an AND-antecedent).
;;; -----------------------------------------------------------------------
;;; bt-succ-minus-1 MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.
;;; bt-sum-in-carr-zz MOVED 2026-09-15 (wave 7) to theorem-library/comb-kk-laws.scm, where it is PROVEN modulo 0 -- reachable because COMB-KK is now ZZ-indexed, as this file's own header always said.
;;; bt-add-in-carr is PROVEN (2026-08-31) in theorem-library/op-typing.scm, with the
;;; other six applied-form op typings: one driver over the IS-X unfold plus
;;; apply-tupling-2 and fun-apply-type-c -- the derivation the warrant here
;;; recited.

