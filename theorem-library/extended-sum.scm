;;; theorem-library/extended-sum.scm -- ESUM: the unordered sum in RR-POS-STAR
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

;;; Totality: ESUM(f) always lands in RR-POS-STAR.  This IS "every f is summable":
;;; the sum is a bona fide element of [0,+inf] for any RR-POS-STAR-valued f.
(theory-add-axiom! *current-theory* 'esum-in
  '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
       (IN (ESUM f) RR-POS-STAR))))

(warrant! 'esum-in 'informal
  "ESUM(f) is the ESUP of the set of finite partial sums of f.  Each partial
   sum FINSUM(RR-POS-STAR-ADD-MONOID, f, S) lies in RR-POS-STAR by finsum-comm-monoid-type
   (RR-POS-STAR-ADD-MONOID is a commutative monoid with carrier RR-POS-STAR), so that set is
   a subset of RR-POS-STAR, and esup-in puts its sup back in RR-POS-STAR.  Hence the sum is
   defined for every RR-POS-STAR-valued f -- every such f is summable.")

;;; Upper bound: every finite partial sum is <= ESUM(f).
(theory-add-axiom! *current-theory* 'esum-upper
  '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
     (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
       (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) (ESUM f)))))))

(warrant! 'esum-upper 'informal
  "Restated esup-upper for the family of finite partial sums: ESUM(f) is by
   definition their supremum in RR-POS-STAR, hence an upper bound for each of them.")

;;; Least upper bound: ESUM(f) lies below any b in RR-POS-STAR that bounds all the
;;; finite partial sums.  Together with esum-upper this pins ESUM(f) uniquely
;;; (antisymmetry of <=).
(theory-add-axiom! *current-theory* 'esum-least
  '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
     (FORALL b (IMPLIES (AND (IN b RR-POS-STAR)
                  (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
                    (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) b))))
       (<= (ESUM f) b))))))

(warrant! 'esum-least 'informal
  "Restated esup-least for the family of finite partial sums: the supremum is
   below every upper bound b that itself lies in RR-POS-STAR.")

;;; -----------------------------------------------------------------------
;;; Finiteness dichotomy -- the user's spec: the sum is +inf unless the
;;; summands are finitely summable.  ESUM(f) is a real (finite) iff the finite
;;; partial sums are bounded above by some real M; otherwise, being in RR-POS-STAR
;;; and above every real bound, it is POS-INF.

(support 'esum-finite-iff-bounded
  '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
     (IFF (IN (ESUM f) RR)
          (FORSOME M (AND (IN M RR)
            (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
              (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M)))))))))

(warrant! 'esum-finite-iff-bounded 'informal
  "Both directions from the characterizing laws plus RR-POS-STAR = RR u {POS-INF}.
   (=>) If ESUM(f) in RR, then by esum-upper every partial sum is <= ESUM(f),
   so M = ESUM(f) is a real bound.  (<=) If a real bound M exists, esum-least
   gives ESUM(f) <= M; and ESUM(f) in RR-POS-STAR with ESUM(f) <= M < POS-INF forces
   ESUM(f) =/= POS-INF, hence ESUM(f) in RR.  Contrapositive: ESUM(f) = POS-INF
   exactly when the partial sums admit no real bound -- the sum is +inf unless
   f is finitely summable.")
