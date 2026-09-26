;;; pw-integral.scm -- the primitive with a FINITE exceptional set, the
;;; CC-valued integral, paths and roads.  VOCABULARY ONLY: nothing is proven
;;; here.  The laws are theorem-library/pw-integral-laws.scm (stage 1),
;;; theorem-library/cc-int-laws.scm (stage 2) and theorem-library/road-laws.scm
;;; (stage 3).
;;;
;;; Design note: docs/paths-and-line-integrals-2026-09-21.md, sections 3.2, 3.3,
;;; 3.4, with the decisions of sections 4 and 5 (user, 2026-09-21):
;;;   4.1  the exceptional set is FINITE -- a partition, not a denumerable set;
;;;   4.2  the endpoints of the interval belong to it;
;;;   4.3  the integral along a road is Dieudonne's, f(gamma(t)) gamma'(t)
;;;        integrated over [a, b], taken componentwise;
;;;   4.4  the names IS-PATH (continuous) and IS-ROAD (piecewise
;;;        regulated-differentiable), after Dieudonne 9.6;
;;;   5.1  a path is `gamma in FUN(RR, CC)' with the interval as two PARAMETERS,
;;;        the convention of the whole real calculus in this tree
;;;        (IS-ANTIDERIVATIVE, IS-REGULATED, C-INT and the sixty results about
;;;        them), not `gamma in FUN(CCINT(a,b), CC)';
;;;   5.2  the derivative `dgamma' is an EXPLICIT argument of IS-ROAD, as `L' is
;;;        of IS-DIFF-AT: gamma' is not determined at the partition points, so an
;;;        IOTA-defined gamma' would be undefined there;
;;;   5.3  `dgamma' is piecewise continuous WITH one-sided limits at the
;;;        partition points, not merely regulated.
;;;
;;; WHAT IS DEFINED HERE
;;;
;;;   IS-PW-ANTIDERIVATIVE(pf, phi, a, b)   Dieudonne 8.7's primitive with the
;;;                                         exceptional set finite (3.2)
;;;   IS-PW-ANTIDERIVABLE(phi, a, b)        some pf does it
;;;   PW-INT(phi, a, b)                     the IOTA, as C-INT is built
;;;   CC-INT(phi, a, b)                     equation (44) of the user's notes
;;;   IS-PATH(pgam, a, b)                   Dieudonne 9.6
;;;   IS-ROAD(pgam, dgam, a, b)             Dieudonne 9.6, decision 5.3
;;;   TRACE(pgam, a, b)                     the image of the interval
;;;   LINE-INT(pf, pgam, dgam, a, b)        the integral along a road
;;;
;;; ---------------------------------------------------------------------------
;;; THE STATEMENT CHECKS (CLAUDE.md, "the species of FALSE or underdetermined
;;; support"), run BEFORE anything below was proven:
;;;
;;; * EVERY index is typed and `SUCC' is applied only on NN.  In
;;;   IS-PW-ANTIDERIVATIVE the index `idx_' is guarded by
;;;   `(IN idx_ (INTERVAL 0 npc_))', and `interval-elt-in-nn' makes it a natural;
;;;   IS-PARTITION types `prt_' as a member of FUN(NN, RR), TOTAL on NN, so
;;;   `prt_(SUCC idx_)' is an application of a function to a point of its domain.
;;;   The number of pieces `npc_' is typed (IN npc_ NN) and bounded below
;;;   (1 <= npc_) by IS-PARTITION itself.  `tv_' is typed (IN tv_ RR) before
;;;   `phi(tv_)' is written.  This is the shape of IS-PIECEWISE-CONTINUOUS
;;;   (structure-library/regulated.scm) character for character, which is
;;;   deliberate: the two predicates are read by the same drivers.
;;;
;;; * PW-INT is a DEFINITE DESCRIPTION (IOTA), not a CHOICE.  Its uniqueness
;;;   obligation -- any two PW-antiderivatives of one phi on [a, b] have the same
;;;   endpoint difference -- is `pw-antiderivative-endpoint-difference', PROVEN in
;;;   theorem-library/pw-integral-laws.scm.  It is not assumed anywhere.
;;;   The IOTA body opens with `(IN vv_ RR)', the rule the eight
;;;   description-defined functoids of the tree agree on: IS-PW-ANTIDERIVATIVE
;;;   says nothing about vv_, so the typing conjunct has to be explicit (the same
;;;   reason c-int.scm gives).
;;;
;;; * EXISTENCE is not claimed.  The description is undefined where phi has no
;;;   PW-antiderivative, which is the tree's normal treatment of a partial
;;;   operator (`=' is partial in VNB).  Consequently EVERY law about PW-INT is
;;;   stated under the hypothesis IS-PW-ANTIDERIVABLE(phi, a, b) -- or with an
;;;   IS-PW-ANTIDERIVATIVE in hand -- exactly as the C-INT laws are stated under
;;;   IS-ANTIDERIVABLE.  A strict `=' on an IOTA term with no such hypothesis
;;;   would ASSERT definedness, which is the species of falsity `finsum-congruence'
;;;   was repaired for.
;;;
;;; * BINDERS.  MIT Scheme and the VNB reader fold case, so `F' and `f' are one
;;;   symbol; no binder here is spelled like a class name (the fatal
;;;   `constant-binder-audit' tests NN ZZ QQ RR CC ORD SET EMPTY-SET POS-INF
;;;   NEG-INF RR-STAR RR-POS-STAR), like a structure accessor (CARR, PTS, DIST,
;;;   IDEN) or like a registered constant.  The bound names are `xv_', `tv_',
;;;   `vv_', `npc_', `prt_', `idx_', `pf_'; the parameters are `pf', `phi', `a',
;;;   `b', `pgam', `dgam'.  `prt_' is NOT `p' and `npc_' is NOT `n' on purpose: a
;;;   driver that rebuilds one of these terms must use binders nothing else binds,
;;;   or `subst-free' renames them and every later `equal?' lookup silently misses.
;;;
;;; * NO NEW AXIOM, NO STAMP, NO SUPPORT.  `def-predicate' and `def-constant'
;;;   install a definitional THEOREM (contributing {} to every bill);
;;;   `def-functoid' installs a rewrite macete.  Nothing here is asserted.
;;;
;;; THE ONE TRAP UNDER `def-functoid' (CLAUDE.md, "Where a definition lives"):
;;; `mac' unfolds PW-INT / CC-INT / TRACE / LINE-INT in a GOAL, but `mac-h'
;;; CANNOT unfold one in an ASSUMPTION by the functoid's own name.  The cure, when
;;; it is needed, is to PROVE the unfold equation as a one-line theorem; the laws
;;; files do that where a hypothesis has to be opened.
;;;
;;; WHERE IT LOADS.  After structure-library/regulated (IS-PARTITION,
;;; IS-PIECEWISE-CONTINUOUS), structure-library/antiderivative (the reading of
;;; IS-ANTIDERIVATIVE this mirrors), structure-library/derivative (IS-DIFF-AT),
;;; structure-library/complex (CC-MS) and number-systems (CC, real-part,
;;; imag-part, +i, IMAGE, CCINT).  Nothing below regulated is needed and nothing
;;; yet stated anywhere cites these heads, so the slot is immediately before
;;; theorem-library/pw-integral-laws at the end of the theorem block.

;;; ===========================================================================
;;; 3.2  THE PRIMITIVE WITH A FINITE EXCEPTIONAL SET
;;; ===========================================================================

;;; IS-PW-ANTIDERIVATIVE(pf, phi, a, b):  pf and phi are total real functions,
;;; a < b, pf is continuous at every point of [a, b], and there is a partition of
;;; [a, b] such that pf is differentiable with derivative phi(t) at every t
;;; INTERIOR to a piece.  The partition points -- the two endpoints among them,
;;; decision 4.2 -- are the exceptional set, and no derivative is ever taken at
;;; one, so no one-sided derivative is needed.  This agrees with the decision of
;;; 2026-09-20 that the domain of differentiation is OPEN.
(def-predicate 'IS-PW-ANTIDERIVATIVE '(pf phi a b)
  (conjuncts->and
    (list '(IN pf (FUN RR RR))
          '(IN phi (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORALL xv_ (IMPLIES (IN xv_ (CCINT a b))
                        (IS-CONTINUOUS-AT RR-MS RR-MS pf xv_)))
          '(FORSOME npc_ (FORSOME prt_
             (AND (IS-PARTITION prt_ npc_ a b)
                  (FORALL idx_
                    (IMPLIES (AND (IN idx_ (INTERVAL 0 npc_)) (< idx_ npc_))
                      (FORALL tv_
                        (IMPLIES (AND (IN tv_ RR)
                                 (AND (< (prt_ idx_) tv_) (< tv_ (prt_ (SUCC idx_)))))
                                 (IS-DIFF-AT pf tv_ (phi tv_)))))))))))))

(def-predicate 'IS-PW-ANTIDERIVABLE '(phi a b)
  '(FORSOME pf_ (IS-PW-ANTIDERIVATIVE pf_ phi a b)))

;;; PW-INT(phi, a, b) = pf(b) - pf(a) for any PW-antiderivative pf.  Built as
;;; C-INT is (theorem-library/c-int.scm): a definite description whose body pins
;;; the value's membership with an explicit conjunct.
(def-functoid 'PW-INT '(phi a b)
  '(IOTA vv_ (AND (IN vv_ RR)
                  (FORSOME pf_ (AND (IS-PW-ANTIDERIVATIVE pf_ phi a b)
                                    (= vv_ (- (pf_ b) (pf_ a))))))))

;;; ===========================================================================
;;; 3.3  THE INTEGRAL OF A CC-VALUED FUNCTION -- equation (44) of the notes
;;; ===========================================================================

;;; CC-INT(phi, a, b) = PW-INT(re o phi, a, b) + PW-INT(im o phi, a, b) * i.
;;; The coordinate maps are written as the VNB-LAMBDAs `t |-> real-part(phi(t))'
;;; and `t |-> imag-part(phi(t))', which is the shape IS-CC-DIFF-AT
;;; (structure-library/cc-coords.scm) uses, so the two developments meet without
;;; a transfer.  Written `x + y*i' and not `x + i*y' to match cc-of-pair-def and
;;; cc-re-im-of.
(def-functoid 'CC-INT '(phi a b)
  '(+ (PW-INT (VNB-LAMBDA tv_ RR (real-part (phi tv_))) a b)
      (* (PW-INT (VNB-LAMBDA tv_ RR (imag-part (phi tv_))) a b) +i)))

;;; ===========================================================================
;;; 3.4  PATHS AND ROADS
;;; ===========================================================================

;;; A PATH is a continuous map of [a, b] into CC (Dieudonne 9.6).  Dieudonne also
;;; asks that it not be reduced to a point; that is not stated here, because
;;; nothing below needs it and `a < b' already excludes the degenerate interval.
(def-predicate 'IS-PATH '(pgam a b)
  (conjuncts->and
    (list '(IN pgam (FUN RR CC))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORALL xv_ (IMPLIES (IN xv_ (CCINT a b))
                        (IS-CONTINUOUS-AT RR-MS CC-MS pgam xv_))))))

;;; A ROAD is a path that is a primitive of a piecewise continuous dgam, taken
;;; componentwise (decisions 4.3 and 5.3).  The one-sided-limit half of 5.3 is
;;; spelled IS-REGULATED: a piecewise continuous function has both one-sided
;;; limits at every NON-partition point for free (continuity gives them), so
;;; IS-PIECEWISE-CONTINUOUS together with IS-REGULATED is exactly "piecewise
;;; continuous with one-sided limits at the partition points" in the vocabulary
;;; the tree already has.  It is what the existence of the primitive of the
;;; integrand will need (c-int-defined-for-continuous on each piece, the extension
;;; to the closed piece coming from the one-sided limits).
(def-predicate 'IS-ROAD '(pgam dgam a b)
  (conjuncts->and
    (list '(IS-PATH pgam a b)
          '(IN dgam (FUN RR CC))
          '(IS-PIECEWISE-CONTINUOUS (VNB-LAMBDA tv_ RR (real-part (dgam tv_))) a b)
          '(IS-PIECEWISE-CONTINUOUS (VNB-LAMBDA tv_ RR (imag-part (dgam tv_))) a b)
          '(IS-REGULATED (VNB-LAMBDA tv_ RR (real-part (dgam tv_))) a b)
          '(IS-REGULATED (VNB-LAMBDA tv_ RR (imag-part (dgam tv_))) a b)
          '(IS-PW-ANTIDERIVATIVE (VNB-LAMBDA tv_ RR (real-part (pgam tv_)))
                                 (VNB-LAMBDA tv_ RR (real-part (dgam tv_))) a b)
          '(IS-PW-ANTIDERIVATIVE (VNB-LAMBDA tv_ RR (imag-part (pgam tv_)))
                                 (VNB-LAMBDA tv_ RR (imag-part (dgam tv_))) a b))))

;;; The TRACE of a path: the image of the parameter interval.  A functoid, so
;;; `mac' unfolds it in a goal.
(def-functoid 'TRACE '(pgam a b)
  '(IMAGE pgam (CCINT a b)))

;;; The integral of pf along the road (pgam, dgam) over [a, b] -- Dieudonne's
;;; definition, decision 4.3.  `pf' is a CC-valued function defined (at least) on
;;; the trace; the integrand t |-> pf(gamma(t)) * dgam(t) is a map RR -> CC and
;;; CC-INT integrates it componentwise.
(def-functoid 'LINE-INT '(pf pgam dgam a b)
  '(CC-INT (VNB-LAMBDA tv_ RR (* (pf (pgam tv_)) (dgam tv_))) a b))

;;; ===========================================================================
;;; Notation.  A head with no `notation!' shows in the Focus workspace as
;;; "(no English reading declared)", so an undeclared reading is a hole the
;;; reader sees, not merely a gap in a table.
;;; ===========================================================================

(notation! 'IS-PW-ANTIDERIVATIVE 'kind 'predicate 'arity 4
           'english "$1 is a piecewise antiderivative of $2 on the interval [$3, $4]")
(notation! 'IS-PW-ANTIDERIVABLE 'kind 'predicate 'arity 3
           'english "$1 has a piecewise antiderivative on the interval [$2, $3]")
(notation! 'PW-INT 'kind 'functoid 'arity 3
           'english "the piecewise integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")
(notation! 'CC-INT 'kind 'functoid 'arity 3
           'english "the complex integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")
(notation! 'IS-PATH 'kind 'predicate 'arity 3
           'english "$1 is a path on the interval [$2, $3]")
(notation! 'IS-ROAD 'kind 'predicate 'arity 4
           'english "$1 is a road with derivative $2 on the interval [$3, $4]")
(notation! 'TRACE 'kind 'functoid 'arity 3
           'english "the trace of the path $1 on [$2, $3]")
(notation! 'LINE-INT 'kind 'functoid 'arity 5
           'english "the integral of $1 along the road $2 with derivative $3 from $4 to $5")
