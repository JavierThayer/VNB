;;; regulated-primitive.scm -- COUNTABLE SETS, ONE-SIDED LIMITS WITHIN A SET,
;;; REGULATED FUNCTIONS ON AN INTERVAL, PRIMITIVES.  DEFINITIONS ONLY; the laws
;;; are PROVEN in theorem-library/regulated-primitive-laws.scm.
;;;
;;; THE SPECIFICATION is docs/roads-regulated-primitives-2026-09-23.md (the
;;; user's decision of 2026-09-23).  The source is Dieudonne, Foundations of
;;; Modern Analysis:
;;;
;;;   VII.6  "For any mapping f of I into F and any point x in I distinct from
;;;          b, we say that f has a limit on the right if lim_{y in I, y > x,
;;;          y -> x} f(y) exists [...].  A mapping f of I into F is called a
;;;          regulated function if it has one-sided limits at every point of I."
;;;   VIII.7 "We say that a continuous mapping g of I into F is a primitive of
;;;          f in I if there exists a denumerable set D c I such that, for any
;;;          xi in I - D, g is differentiable at xi and g'(xi) = f(xi)."
;;;
;;;     IS-COUNTABLE(D)                      D is a set, empty or the image of
;;;                                          a function on NN ("at most
;;;                                          denumerable", Dieudonne 1.9)
;;;     IS-RIGHT-LIMIT-WITHIN(f, W, x, l)    f, a function on W, tends to l as
;;;                                          t -> x through the points t > x of W
;;;     IS-LEFT-LIMIT-WITHIN(f, W, x, l)     the same through the points t < x
;;;     IS-REGULATED-ON(f, a, b)             f, a function ON [a,b], has a right
;;;                                          limit within [a,b] at every x < b and
;;;                                          a left limit at every x > a
;;;     IS-PRIMITIVE(g, f, a, b)             g continuous on [a,b], g'(t) = f(t)
;;;                                          at every interior t off a COUNTABLE
;;;                                          set D contained in [a,b]
;;;
;;; STATEMENT CHECKS (CLAUDE.md, species of false or underdetermined support):
;;;
;;; (1) "Denumerable" in 8.5.1 / 8.7 is used for sets that may be finite (the
;;;     finite version of the constancy lemma is its special case), so the
;;;     predicate is "at most denumerable".  It is phrased by a SURJECTION from
;;;     NN, not a bijection: every finite nonempty set is such an image (repeat
;;;     a point), and no injectivity is ever used by 8.5.1 (the weights 2^-n
;;;     only need to be summable).  The empty set is a separate disjunct because
;;;     FUN(NN, EMPTY-SET) is empty.  `(IN rpc_ SET)' excludes a proper class.
;;; (2) The one-sided limits carry the function's domain W as an argument and
;;;     type the function ON W (`f in FUN(W, RR)'): the limit of a function given
;;;     only on a set, the point x not necessarily in W.  W is a set of reals
;;;     (`SUBSET W RR').  The value l is typed.  Where x is NOT a limit point of
;;;     W from that side, every real l is a limit (vacuity, as in Dieudonne's
;;;     "x distinct from b"): uniqueness is a theorem with that hypothesis
;;;     (`right-limit-within-unique').  The inequality is STRICT, |f(t)-l| < eps,
;;;     on the open window x < t < x + delta, as the design note words it.
;;; (3) IS-REGULATED-ON guards the right limit on x < b and the left one on
;;;     a < x, which is Dieudonne's "x distinct from b" / "distinct from a".
;;;     The two requirements are SEPARATE conjuncts (a `fact' on either needs no
;;;     conjunction split).  The 2026-09-08 IS-REGULATED (total f in FUN(RR,RR),
;;;     structure-library/regulated.scm) is not touched.
;;; (4) IS-PRIMITIVE is IS-PW-ANTIDERIVATIVE (path-integral.scm) with the
;;;     finiteness `CARD(S) in NN' replaced by IS-COUNTABLE.  The derivative is
;;;     required at the INTERIOR points off D only (OOINT), as there: Dieudonne's
;;;     derivative "with respect to I" at an endpoint is the one-sided one, and
;;;     putting the endpoints into D (countable) costs nothing.
;;; (5) Binders are prefixed `rp' and occur in no other predicate body; none
;;;     folds onto a class name or a registered constant.  `f' and `g' are the
;;;     parameters `rpf_' / `rpg_' (F and f are one symbol).
;;; (6) Antecedents are CURRIED.
;;;
;;; Dependencies: cardinality.scm (SET, EMPTY-SET), extreme-value.scm (CCINT),
;;; interval-calculus.scm (OOINT, IS-CONTINUOUS-ON, HAS-DERIV-AT), number
;;; systems (NN, RR, ABS, POS-RR).  Loads right after
;;; structure-library/interval-calculus.

;;; -----------------------------------------------------------------------
;;; IS-COUNTABLE(D) -- at most denumerable (Dieudonne 1.9).
(def-predicate 'IS-COUNTABLE '(rpc_)
  '(AND (IN rpc_ SET)
        (OR (= rpc_ EMPTY-SET)
            (FORSOME rpen_
              (AND (IN rpen_ (FUN NN rpc_))
                   (FORALL rpy_
                     (IMPLIES (IN rpy_ rpc_)
                       (FORSOME rpn_ (AND (IN rpn_ NN) (= rpy_ (rpen_ rpn_)))))))))))

(notation! 'IS-COUNTABLE 'kind 'predicate 'arity 1
           'english "$1 is countable")

;;; -----------------------------------------------------------------------
;;; IS-RIGHT-LIMIT-WITHIN(f, W, x, l) -- lim_{t in W, t > x, t -> x} f(t) = l.
(def-predicate 'IS-RIGHT-LIMIT-WITHIN '(rpf_ rpw_ rpx_ rpl_)
  (conjuncts->and
    (list '(SUBSET rpw_ RR)
          '(IN rpf_ (FUN rpw_ RR))
          '(IN rpx_ RR)
          '(IN rpl_ RR)
          '(FORALL rpe_
             (IMPLIES (POS-RR rpe_)
               (FORSOME rpdl_
                 (AND (POS-RR rpdl_)
                      (FORALL rpt_
                        (IMPLIES (IN rpt_ rpw_)
                          (IMPLIES (< rpx_ rpt_)
                            (IMPLIES (< rpt_ (+ rpx_ rpdl_))
                              (< (ABS (- (rpf_ rpt_) rpl_)) rpe_))))))))))))

(notation! 'IS-RIGHT-LIMIT-WITHIN 'kind 'predicate 'arity 4
           'english "$1 has right limit $4 at $3 within $2")

;;; IS-LEFT-LIMIT-WITHIN(f, W, x, l) -- lim_{t in W, t < x, t -> x} f(t) = l.
(def-predicate 'IS-LEFT-LIMIT-WITHIN '(rpf_ rpw_ rpx_ rpl_)
  (conjuncts->and
    (list '(SUBSET rpw_ RR)
          '(IN rpf_ (FUN rpw_ RR))
          '(IN rpx_ RR)
          '(IN rpl_ RR)
          '(FORALL rple_
             (IMPLIES (POS-RR rple_)
               (FORSOME rpld_
                 (AND (POS-RR rpld_)
                      (FORALL rplt_
                        (IMPLIES (IN rplt_ rpw_)
                          (IMPLIES (< (- rpx_ rpld_) rplt_)
                            (IMPLIES (< rplt_ rpx_)
                              (< (ABS (- (rpf_ rplt_) rpl_)) rple_))))))))))))

(notation! 'IS-LEFT-LIMIT-WITHIN 'kind 'predicate 'arity 4
           'english "$1 has left limit $4 at $3 within $2")

;;; -----------------------------------------------------------------------
;;; IS-REGULATED-ON(f, a, b) -- Dieudonne VII.6 on the compact interval [a,b].
(def-predicate 'IS-REGULATED-ON '(rpf_ rpa_ rpb_)
  (conjuncts->and
    (list '(IN rpa_ RR)
          '(IN rpb_ RR)
          '(< rpa_ rpb_)
          '(IN rpf_ (FUN (CCINT rpa_ rpb_) RR))
          '(FORALL rpx_
             (IMPLIES (IN rpx_ (CCINT rpa_ rpb_))
               (IMPLIES (< rpx_ rpb_)
                 (FORSOME rpl_
                   (IS-RIGHT-LIMIT-WITHIN rpf_ (CCINT rpa_ rpb_) rpx_ rpl_)))))
          '(FORALL rpx_
             (IMPLIES (IN rpx_ (CCINT rpa_ rpb_))
               (IMPLIES (< rpa_ rpx_)
                 (FORSOME rpl_
                   (IS-LEFT-LIMIT-WITHIN rpf_ (CCINT rpa_ rpb_) rpx_ rpl_))))))))

(notation! 'IS-REGULATED-ON 'kind 'predicate 'arity 3
           'english "$1 is regulated on the interval [$2, $3]")

;;; -----------------------------------------------------------------------
;;; IS-PRIMITIVE(g, f, a, b) -- Dieudonne VIII.7 on the compact interval [a,b].
(def-predicate 'IS-PRIMITIVE '(rpg_ rpf_ rpa_ rpb_)
  (conjuncts->and
    (list '(IN rpa_ RR)
          '(IN rpb_ RR)
          '(< rpa_ rpb_)
          '(IN rpg_ (FUN (CCINT rpa_ rpb_) RR))
          '(IN rpf_ (FUN (CCINT rpa_ rpb_) RR))
          '(IS-CONTINUOUS-ON rpg_ (CCINT rpa_ rpb_))
          '(FORSOME rps_
             (AND (IS-COUNTABLE rps_)
             (AND (SUBSET rps_ (CCINT rpa_ rpb_))
                  (FORALL rpt_
                    (IMPLIES (IN rpt_ (OOINT rpa_ rpb_))
                      (IMPLIES (NOT (IN rpt_ rps_))
                        (HAS-DERIV-AT rpg_ rpt_ (rpf_ rpt_)))))))))))

(notation! 'IS-PRIMITIVE 'kind 'predicate 'arity 4
           'english "$1 is a primitive of $2 on the interval [$3, $4]")
