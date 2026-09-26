;;; extended-arith.scm -- the rest of the arithmetic and order vocabulary of
;;; RR-POS-STAR = [0, +inf]: multiplication, infima, and the limit operations of a
;;; sequence.
;;;
;;; extended-reals-pos.scm gives [0,+inf] its carrier, its order, the supremum
;;; ESUP and extended ADDITION.  That is everything unordered summation needs
;;; and not enough for measure theory, which also wants
;;;
;;;   * a PRODUCT (alpha times the integral of f; the simple-function integral
;;;     as a sum of terms alpha_i times mu(A_i)) -- `etimes' below;
;;;   * an INFIMUM (continuity of a measure from above; the inner half of
;;;     lim inf) -- `EINF' below, built from ESUP as the sup of the lower
;;;     bounds, which is the standard construction in a complete lattice and
;;;     needs no new axiom;
;;;   * LIM INF and LIM SUP of a sequence -- Fatou's lemma is about nothing
;;;     else -- and hence a notion of CONVERGENCE in [0,+inf].
;;;
;;; WHERE THIS FILE SITS.  Conceptually it belongs immediately after
;;; extended-reals-pos.scm.  It is loaded much later, beside the measure files
;;; it serves, for one concrete reason: ETAIL is built from IMAGE, whose
;;; membership law lives in injection.scm, which loads after extended-reals-pos.
;;;
;;; PROVENANCE (REWRITTEN 2026-09-18).  The paragraph below is kept as the record of a
;;; mistake: it argued that the five etimes equations were "a definition by cases of a
;;; fresh symbol" and stamped them `definitional'.  They were not a definition -- one of
;;; them was false (see ETIMES, DEFINED below) -- and the stamp hid it from every bill.
;;; etimes is now defined by ONE quasi-equation and its laws are proven.
;;; [old text:] Everything below except `etimes-in-fun' is FREE.  The five
;;; etimes equations are a definition by cases of a fresh symbol -- exhaustive
;;; over RR-POS-STAR x RR-POS-STAR and pairwise disjoint, since POS-INF is not a real
;;; (pos-inf-not-in-rr) and the absorbing clauses exclude 0 explicitly -- so
;;; they are wrapped `definitional' and contribute {} to every bill.  The five
;;; order/limit operators are `def-functoid's, hence definitional by
;;; construction.  `etimes-in-fun' is deliberately outside the definitional
;;; block: it claims the graph is a SET and the operation TOTAL, which is a
;;; sethood claim rather than a definition, and it carries its own warrant --
;;; the same status eplus-in-fun has in extended-reals-pos.scm.
;;;
;;; Dependencies: extended-reals.scm (POS-INF), extended-reals-pos.scm (RR-POS-STAR,
;;; ESUP, eplus), numeric-instances.scm (bintimes), number-systems.scm (RR, NN,
;;; 0, <=), injection.scm (IMAGE).  ETIMES is registered as a term-form head in
;;; wff.scm.
;;; ====================================================================

;;; -----------------------------------------------------------------------
;;; etimes : RR-POS-STAR x RR-POS-STAR -> RR-POS-STAR
;;;
;;; THE CONVENTION.  0 * (+inf) = 0.  Not a theorem and not a debt: it is the
;;; definition measure theory chooses, precisely so that the integral of the
;;; function identically +inf over a null set is 0 (Thayer, Construction of
;;; Measures, Thm. 2.7, property (3), p. 10).  Rudin states it in as many
;;; words -- "The convention 0 * inf = 0 is used here" -- in the paragraph
;;; defining the integral of a simple function (Rudin, Real and Complex
;;; Analysis, Def. 1.23, p. 19).

;;; ETIMES, DEFINED (2026-09-18, rake batch 5c-Y).  The five case equations that stood here,
;;; wrapped `definitional', and the typing axiom `etimes-in-fun' were jointly INCONSISTENT:
;;; `etimes-real' concluded a strict `=' for ALL reals, so etimes(x,0) denoted for every real
;;; x, while `etimes-in-fun' made etimes a function defined exactly on [0,+oo] x [0,+oo]; so
;;; every real was >= 0 (probe: scratchpad/r7y/r7y-p1.scm).  Worse than EPLUS: the stamp made
;;; the false equation contribute {} to every bill, so no ledger could show it.  The old
;;; forms are in archive/retired-2026-09-18/extended-arith--etimes-axioms.scm.  Every law is
;;; now a THEOREM of the definition below (theorem-library/rake-etimes-defined.scm): the four
;;; infinite-case equations and etimes-in-fun with statements unchanged, and
;;; `etimes-real-defined', which carries the guards 0 <= x, 0 <= y.  The convention
;;; 0 * oo = 0 is the one the old equations stated.
(declare-named-only! 'etimes-def
  "left-hand side is a bare constant: as a live rewrite it would turn every mention of etimes into its lambda")
(fluid-let ((*current-provenance* 'definitional))
  (add-axiom! *library* 'etimes-def
    '(== etimes
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR-POS-STAR RR-POS-STAR)
           (IF (OR (= x_ POS-INF) (= y_ POS-INF))
               (IF (OR (= x_ 0) (= y_ 0))
                   0
                   POS-INF)
               (bintimes x_ y_))))))


(gloss! 'etimes-in-fun
  "etimes is a total function from RR-POS-STAR x RR-POS-STAR to RR-POS-STAR: the product of two
   elements of [0,+inf] is again an element of [0,+inf].")

;; Register the head with its PARAMETER NAMES before declaring notation.  A
;; head seeded from *wff-term-form-heads* (wff.scm) reaches the constant
;; registry but not the operator table, and `notation!' on such a head would
;; enter it with no params and kind `primitive' -- which prints as "etimes()"
;; and, worse, files it with the kernel relations (=, IN, <=) instead of with
;; ESUM and ESUP, whose five defining axioms the operator census would then
;; stop listing.  Kind `operator' is what the seed gives ESUM and ESUP.
(register-operator! 'etimes 'operator '(x y))
(notation! 'etimes 'english "$1 times $2 in the extended reals")

;;; -----------------------------------------------------------------------
;;; ELOWER-BOUNDS(S) and EINF(S) -- the greatest lower bound in RR-POS-STAR.
;;;
;;; RR-POS-STAR is a complete lattice: ESUP exists for every subset (esup-in /
;;; esup-upper / esup-least, extended-reals-pos.scm), so the infimum of S is
;;; the SUPREMUM OF THE LOWER BOUNDS of S, and no separate axiom is needed.
;;; Note the boundary case that makes the construction total: the lower bounds
;;; of the EMPTY set are all of RR-POS-STAR, whose sup is POS-INF -- the conventional
;;; value of an empty infimum -- and the lower bounds of any S are nonempty
;;; because 0 is one (rr-pos-star-nonneg).

(def-functoid 'ELOWER-BOUNDS '(S)
  '(SEP b_ RR-POS-STAR (FORALL x_ (IMPLIES (IN x_ S) (<= b_ x_)))))

(def-functoid 'EINF '(S)
  '(ESUP (ELOWER-BOUNDS S)))

(notation! 'ELOWER-BOUNDS 'kind 'functoid 'arity 1
           'english "the set of lower bounds of $1 in the extended reals")
(notation! 'EINF 'kind 'functoid 'arity 1
           'english "the infimum of $1 in the extended reals")

;;; -----------------------------------------------------------------------
;;; ETAIL(f, n) -- the set of values of the sequence f from index n on.
;;;
;;; f is a sequence in RR-POS-STAR, i.e. a member of FUN(NN, RR-POS-STAR); ETAIL(f, n) is
;;; { f(p) : p in NN, n <= p }.  It is the one ingredient lim inf and lim sup
;;; need beyond ESUP and EINF.

(def-functoid 'ETAIL '(f n)
  '(IMAGE f (SEP p_ NN (<= n p_))))

(notation! 'ETAIL 'kind 'functoid 'arity 2
           'english "the set of values of the sequence $1 from index $2 on")

;;; -----------------------------------------------------------------------
;;; ELIMINF(f) and ELIMSUP(f) -- the two one-sided limits of a sequence in
;;; RR-POS-STAR, written exactly as the sources define them:
;;;
;;;   lim inf a_n = lim_n inf_{p >= n} a_p = sup_n inf_{p >= n} a_p
;;;   lim sup a_n = lim_n sup_{p >= n} a_p = inf_n sup_{p >= n} a_p
;;;
;;; (Thayer, Construction of Measures, Eqs. (37) and (38), p. 17, with
;;; Remark 2.25 noting that the limits exist because the inner sequences are
;;; monotone; Rudin, Real and Complex Analysis, Def. 1.13, p. 14.)  In [0,+inf]
;;; the outer limit IS the sup (resp. inf), since the inner family is monotone
;;; and the space is order-complete -- which is why these are definitions here
;;; and not theorems.

(def-functoid 'ELIMINF '(f)
  '(ESUP (IMAGE (VNB-LAMBDA n_ NN (EINF (ETAIL f n_))) NN)))

(def-functoid 'ELIMSUP '(f)
  '(EINF (IMAGE (VNB-LAMBDA n_ NN (ESUP (ETAIL f n_))) NN)))

(notation! 'ELIMINF 'kind 'functoid 'arity 1
           'english "the lower limit of the sequence $1")
(notation! 'ELIMSUP 'kind 'functoid 'arity 1
           'english "the upper limit of the sequence $1")

;;; -----------------------------------------------------------------------
;;; ECONVERGES-TO(f, l) -- convergence of a sequence in [0,+inf].
;;;
;;; A sequence in an order-complete space converges exactly when its lower and
;;; upper limits agree, and then that common value is the limit.  Taking this
;;; as the DEFINITION is a divergence from both sources, which define
;;; convergence in the extended reals by neighbourhoods of the extended
;;; topology and then prove the equivalence; VNB has no topology on RR-POS-STAR, and
;;; the order characterisation is the one every statement below actually uses.

(def-predicate 'ECONVERGES-TO '(f l)
  (conjuncts->and
    (list
      '(IN f (FUN NN RR-POS-STAR))
      '(IN l RR-POS-STAR)
      '(= (ELIMINF f) l)
      '(= (ELIMSUP f) l))))

(notation! 'ECONVERGES-TO 'kind 'predicate 'arity 2
           'english "the sequence $1 converges to $2 in the extended reals")
