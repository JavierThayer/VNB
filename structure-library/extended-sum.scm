;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; structure-library/extended-sum.scm -- ESUM: the unordered sum in RR-POS-STAR
;;;
;;; For a function f : DOM(f) -> RR-POS-STAR on an arbitrary index set, ESUM(f) is
;;; its unordered sum -- the supremum, in the order-complete space RR-POS-STAR, of
;;; all FINITE partial sums:
;;;
;;;   ESUM(f) = sup { FINSUM(RR-POS-STAR-ADD-MONOID, f, S) : S finite subset of DOM f }.
;;;
;;; This is the textbook [0,+inf]-valued sum of nonnegative "measure" data:
;;; every f is summable (the sup always exists because RR-POS-STAR is order-complete
;;; and POS-INF tops it), and ESUM(f) = POS-INF exactly when the partial sums
;;; are unbounded -- i.e. f is summable to a finite value iff its partial sums
;;; are bounded by a real (esum-finite-iff-bounded below).  Order on the index
;;; set is never seen, so the sum is unconditional by construction.
;;;
;;; ESUM is characterized, like ESUP / SUP-ORD before it, by three laws --
;;; membership, upper-bound, least-upper-bound -- rather than built by an
;;; explicit set-comprehension; this keeps it representation-independent and
;;; needs no replacement machinery.  Each partial sum lives in RR-POS-STAR by
;;; finsum-comm-monoid-type (RR-POS-STAR-ADD-MONOID is a commutative monoid, carrier
;;; RR-POS-STAR), so the family ESUM ranges over is a subset of RR-POS-STAR and its sup
;;; exists.
;;;
;;; Dependencies: extended-reals-pos.scm (RR-POS-STAR, RR-POS-STAR-ADD-MONOID, ESUP, the
;;; order), finsum.scm (FINSUM), finsum-comm-monoid.scm (the comm-monoid
;;; finsum lemmas), cardinality (CARD/NN finiteness idiom), number-systems
;;; (RR, <=).  ESUM is registered as a term-form head in wff.scm.

;;; -----------------------------------------------------------------------
;;; The three characterizing laws.
;;;
;;; They mirror esup-in / esup-upper / esup-least, specialized to the family
;;; of finite partial sums of f.  A finite subset of DOM f is the usual
;;; idiom: S in SET, CARD S in NN, S subset of DOM f.

;;; ESUM, DEFINED (2026-09-19, the user's decision; rake batch 6-I).  Until then the three
;;; laws esum-in, esum-upper, esum-least were axioms with `informal' warrants that all said
;;; the same sentence: "ESUM(f) is the ESUP of the set of finite partial sums of f".  That
;;; sentence is now the definition, and the three laws are THEOREMS with their statements
;;; unchanged (theorem-library/rake-esum-defined.scm), from the laws of ESUP
;;; (rake-esup-defined.scm), IS-COMM-MONOID(RR-POS-STAR-ADD-MONOID)
;;; (rake-rr-pos-star-monoid.scm) and finsum-comm-monoid-type-ptwise.  The guard inside the
;;; description is associated exactly as in the three statements, so hypotheses transfer.
(def-functoid 'ESUM '(f_)
  '(ESUP (SEP v_ RR-POS-STAR
           (FORSOME t_
             (AND (AND (IN t_ SET)
                       (AND (IN (CARD t_) NN) (SUBSET t_ (DOM f_))))
                  (= v_ (FINSUM RR-POS-STAR-ADD-MONOID f_ t_)))))))
(notation! 'ESUM 'kind 'functoid 'arity 1
           'english "the sum in [0,+inf] of the family $1")

;;; -----------------------------------------------------------------------
;;; Finiteness dichotomy -- the user's spec: the sum is +inf unless the
;;; summands are finitely summable.  ESUM(f) is a real (finite) iff the finite
;;; partial sums are bounded above by some real M; otherwise, being in RR-POS-STAR
;;; and above every real bound, it is POS-INF.

;;; esum-finite-iff-bounded RETIRED 2026-09-18 (rake batch 5b): proven in theorem-library/rake-extended-order.scm

