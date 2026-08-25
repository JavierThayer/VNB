;;; integral.scm -- MEASURABLE FUNCTIONS, SIMPLE FUNCTIONS and the INTEGRAL of
;;; a [0,+inf]-valued measurable function, with the three convergence theorems.
;;; Vocabulary plus statements; nothing here is proved.
;;;
;;; SOURCES.  Thayer, Construction of Measures, Chapter 2: Def. 2.1 (measurable
;;; function, p. 8), Prop. 2.3 (pointwise limits, p. 8), Def. 2.4 (step
;;; function, p. 9), Prop. 2.6 (continuous combinations, p. 9), Thm. 2.7 (the
;;; integral and its seven characterising properties, pp. 9-10), Prop. 2.13
;;; (approximation by step functions, p. 12), Prop. 2.16 (monotone convergence,
;;; p. 14), Thm. 2.26 (Fatou, p. 17), Prop. 2.28 (dominated convergence, p. 18).
;;; Rudin, Real and Complex Analysis, Chapter 1: Thm. 1.14 (sup and lim sup of
;;; measurable functions, p. 14), Def. 1.16 (simple function, p. 15), Thm. 1.17
;;; (approximation by simple functions, p. 15), Def. 1.23 (the integral, p. 19),
;;; Prop. 1.24 (its elementary properties, pp. 19-20), Thm. 1.26 (monotone
;;; convergence, p. 21), Thm. 1.28 (Fatou, p. 23), Thm. 1.34 (dominated
;;; convergence, p. 26).
;;;
;;; THE INTEGRAL IS CHARACTERISED, NOT CONSTRUCTED, and the source does it that
;;; way too.  Thayer Thm. 2.7 (p. 9) reads: "there is a UNIQUE function
;;; f |-> integral f dmu defined on the set of all A measurable functions
;;; X -> [0,inf] satisfying the following properties", and lists seven.  VNB
;;; installs INTEGRAL as a term-forming head pinned by those properties, one
;;; support apiece -- the same shape ESUP, SUP-ORD and ESUM already have in
;;; this tree.  Rudin's Def. 1.23 (p. 19) instead CONSTRUCTS it, as the
;;; supremum of the integrals of the simple functions below f; that
;;; construction appears here as the theorem `integral-sup-of-simple', which is
;;; the statement that VNB's characterised operator is Rudin's constructed one.
;;;
;;; A WARNING ABOUT THAYER'S PROPERTY NAMES.  The paragraph after Thm. 2.7
;;; reads "Property (2) is additivity, (3) positive homogeneity, (4)
;;; monotonicity and (5) monotone convergence".  Those labels are displaced by
;;; two from the displayed list, where (4) is additivity, (5) positive
;;; homogeneity, (6) monotonicity and (7) monotone convergence.  Every citation
;;; below refers to the NUMBER OF THE DISPLAYED PROPERTY, not to that
;;; paragraph.
;;;
;;; WHAT VNB'S `IS-MEASURABLE-FN' IS, AND WHY IT IS NOT THE SOURCE'S
;;; DEFINITION.  Both sources define measurability of a function by preimages
;;; of the BOREL sets of the target (Thayer Def. 2.1, p. 8; Rudin Def. 1.3(c),
;;; p. 8), and VNB has that definition -- IS-MEASURABLE-MAP (measure.scm).
;;; It cannot be used here.  The target is RR-POS-STAR = [0,+inf], and a sigma-algebra
;;; on RR-POS-STAR means a POWER(RR-POS-STAR), i.e. a sethood fact for RR-POS-STAR, which this tree
;;; does not have: extended-reals.scm asserts none for RR-STAR and calls it a
;;; class.  So IS-MEASURABLE-FN is defined by the TAIL CRITERION instead --
;;; { x : alpha < f(x) } is measurable for every real alpha -- which in both
;;; sources is a THEOREM equivalent to the definition (Rudin Thm. 1.12(c),
;;; p. 13; Thayer Remark 2.2, p. 8, in its generating-class form).  That is a
;;; deliberate divergence, it is recorded on every statement that uses the
;;; predicate, and closing it is a matter of giving RR-POS-STAR a sethood fact and
;;; taking SIGMA-GENERATED of the tails.
;;;
;;; SIMPLE vs STEP.  Rudin's simple function (Def. 1.16, p. 15) has FINITELY
;;; many values and explicitly excludes +inf from them.  Thayer's step function
;;; (Def. 2.4, p. 9) has COUNTABLY many values and allows +inf.  They are
;;; different classes and the two books build the integral over different ones.
;;; VNB follows RUDIN, because `integral-sup-of-simple' -- the bridge from the
;;; characterisation to a construction -- is Rudin's, and because a finite
;;; range is expressible with CARD and NN whereas "countably many values"
;;; would need a fresh countability predicate.
;;;
;;; POINTWISE OPERATIONS are functoids over an explicit ambient omega
;;; (PTWISE-EPLUS, PTWISE-ETIMES, PTWISE-SCALE, PTWISE-SUP, PTWISE-LIMINF).
;;; A VNB lambda carries its domain -- a lambda without one does not determine
;;; a function -- so omega is an argument of each, not an inference.
;;;
;;; Dependencies: measure.scm (IS-MEASURE), sigma-algebra.scm
;;; (IS-SIGMA-ALGEBRA), extended-arith.scm (etimes, ELIMINF, ECONVERGES-TO),
;;; extended-reals-pos.scm (RR-POS-STAR, ESUP, eplus), injection.scm (IMAGE),
;;; cardinality.scm (CARD), order-predicates.scm (<), and the kernel (SEP,
;;; VNB-LAMBDA, IF, FUN, NN, POWER).  INTEGRAL is registered as a term-form
;;; head in wff.scm.
;;; ====================================================================

;;; -----------------------------------------------------------------------
;;; Pointwise vocabulary.

;;; f + g, computed in [0,+inf].
(def-functoid 'PTWISE-EPLUS '(omega f g)
  '(VNB-LAMBDA x_ omega (eplus (f x_) (g x_))))

;;; f * g, computed in [0,+inf] (so 0 * inf = 0 pointwise).
(def-functoid 'PTWISE-ETIMES '(omega f g)
  '(VNB-LAMBDA x_ omega (etimes (f x_) (g x_))))

;;; c * f for a constant c.
(def-functoid 'PTWISE-SCALE '(omega c f)
  '(VNB-LAMBDA x_ omega (etimes c (f x_))))

;;; The pointwise supremum of a SEQUENCE cF of functions on omega.
(def-functoid 'PTWISE-SUP '(omega cF)
  '(VNB-LAMBDA x_ omega (ESUP (IMAGE (VNB-LAMBDA n_ NN ((cF n_) x_)) NN))))

;;; The pointwise lower limit of a sequence cF of functions on omega.
(def-functoid 'PTWISE-LIMINF '(omega cF)
  '(VNB-LAMBDA x_ omega (ELIMINF (VNB-LAMBDA n_ NN ((cF n_) x_)))))

;;; The indicator (characteristic function) of a subset a of omega -- Rudin's
;;; chi_A, Thayer's 1_A.
(def-functoid 'INDICATOR '(omega a)
  '(VNB-LAMBDA x_ omega (IF (IN x_ a) 1 0)))

(notation! 'PTWISE-EPLUS   'kind 'functoid 'arity 3
           'english "the pointwise sum of $2 and $3 on $1")
(notation! 'PTWISE-ETIMES  'kind 'functoid 'arity 3
           'english "the pointwise product of $2 and $3 on $1")
(notation! 'PTWISE-SCALE   'kind 'functoid 'arity 3
           'english "the function $3 scaled by $2 on $1")
(notation! 'PTWISE-SUP     'kind 'functoid 'arity 2
           'english "the pointwise supremum on $1 of the sequence $2")
(notation! 'PTWISE-LIMINF  'kind 'functoid 'arity 2
           'english "the pointwise lower limit on $1 of the sequence $2")
(notation! 'INDICATOR      'kind 'functoid 'arity 2
           'english "the indicator function of $2 in $1")

;;; PTWISE-LE(omega, f, g) -- f <= g at every point of omega.  A predicate
;;; rather than an inlined universal, because every statement below needs it.
(def-predicate 'PTWISE-LE '(omega f g)
  '(FORALL x_ (IMPLIES (IN x_ omega) (<= (f x_) (g x_)))))

(notation! 'PTWISE-LE 'kind 'predicate 'arity 3
           'english "$2 is pointwise at most $3 on $1")

;;; -----------------------------------------------------------------------
;;; IS-MEASURABLE-FN(omega, cA, f) -- see the header for the divergence this
;;; definition embodies.  The tail { x in omega : alpha < f(x) } is written
;;; with SEP, as everywhere else in this arc.

(def-predicate 'IS-MEASURABLE-FN '(omega cA f)
  (conjuncts->and
    (list
      '(IS-SIGMA-ALGEBRA omega cA)
      '(IN f (FUN omega RR-POS-STAR))
      (forall-guarded '(alpha_) '((IN alpha_ RR))
        '(IN (SEP x_ omega (< alpha_ (f x_))) cA)))))

(notation! 'IS-MEASURABLE-FN 'kind 'predicate 'arity 3
           'english "$3 is a measurable [0,+inf]-valued function on $1 with $2")

;;; IS-SIMPLE-FN(omega, cA, f) -- Rudin Def. 1.16 (p. 15): measurable, finitely
;;; many values, none of them +inf.  Finiteness of the range is the tree's
;;; standard idiom, CARD of the image landing in NN.

(def-predicate 'IS-SIMPLE-FN '(omega cA f)
  (conjuncts->and
    (list
      '(IS-MEASURABLE-FN omega cA f)
      '(IN (CARD (IMAGE f omega)) NN)
      (forall-guarded '(x_) '((IN x_ omega)) '(IN (f x_) RR)))))

(notation! 'IS-SIMPLE-FN 'kind 'predicate 'arity 3
           'english "$3 is a simple measurable function on $1 with $2")

;;; =====================================================================
;;; MEASURABILITY IS PRESERVED.  Rudin Thm. 1.14 (p. 14) and Thayer Prop. 2.6
;;; (p. 9) between them are the closure package.

(support 'measurable-fn-indicator
  (forall-guarded '(omega cA a_)
                  '((IS-SIGMA-ALGEBRA omega cA) (IN a_ cA))
    '(IS-MEASURABLE-FN omega cA (INDICATOR omega a_))))

(warrant! 'measurable-fn-indicator 'reference '(rudin-rca "Def. 1.16" 30))
(topic!   'measurable-fn-indicator 'plumbing)
(gloss!   'measurable-fn-indicator
  "The indicator function of a measurable set is measurable.  Rudin states it
   in the paragraph of Def. 1.16 (p. 15): a simple function is measurable if
   and only if each of the sets on which it is constant is measurable, of
   which this is the two-valued case.  A definitional read-off in either
   source, and asserted here rather than proved because VNB's measurability is
   the tail criterion, so the read-off is a case analysis on alpha rather than
   a rewriting.")

(support 'measurable-fn-eplus
  (forall-guarded '(omega cA f g)
                  '((IS-MEASURABLE-FN omega cA f) (IS-MEASURABLE-FN omega cA g))
    '(IS-MEASURABLE-FN omega cA (PTWISE-EPLUS omega f g))))

(warrant! 'measurable-fn-eplus 'reference '(thayer-measures "Prop. 2.6" 15))
(topic!   'measurable-fn-eplus 'plumbing)
(gloss!   'measurable-fn-eplus
  "The pointwise sum of two measurable [0,+inf]-valued functions is
   measurable.  NOT literally either source's statement.  Thayer Prop. 2.6
   (p. 9) proves it for functions into a METRIC space composed with a
   continuous phi, and remarks 'in particular, sums and products of measurable
   functions are measurable'; Rudin Prop. 1.9(c) (p. 11) states it for COMPLEX
   measurable functions.  Neither covers [0,+inf], where the addition is
   `eplus' and +inf is a value; that case is the routine limit of the
   truncations, and is what VNB asserts.")

(support 'measurable-fn-etimes
  (forall-guarded '(omega cA f g)
                  '((IS-MEASURABLE-FN omega cA f) (IS-MEASURABLE-FN omega cA g))
    '(IS-MEASURABLE-FN omega cA (PTWISE-ETIMES omega f g))))

(warrant! 'measurable-fn-etimes 'reference '(thayer-measures "Prop. 2.6" 15))
(topic!   'measurable-fn-etimes 'plumbing)
(gloss!   'measurable-fn-etimes
  "The pointwise product of two measurable [0,+inf]-valued functions is
   measurable, the product being `etimes' and hence carrying the 0 * inf = 0
   convention.  Same divergence from the sources as measurable-fn-eplus: both
   state the finite-valued case (Thayer Prop. 2.6, p. 9; Rudin Prop. 1.9(c),
   p. 11) and neither states the extended one.")

(support 'measurable-fn-sup
  (forall-guarded '(omega cA cF)
                  (list '(IS-SIGMA-ALGEBRA omega cA)
                        '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(IS-MEASURABLE-FN omega cA (cF n_))))
    '(IS-MEASURABLE-FN omega cA (PTWISE-SUP omega cF))))

(warrant! 'measurable-fn-sup 'reference '(rudin-rca "Thm. 1.14" 29))
(topic!   'measurable-fn-sup 'analysis)
(gloss!   'measurable-fn-sup
  "The pointwise supremum of a sequence of measurable functions is measurable.
   Rudin Thm. 1.14 (p. 14), stated there for [-inf,+inf]-valued functions and
   for sup and lim sup together; VNB states the [0,+inf] case and splits sup
   from lim inf (see measurable-fn-liminf), lim sup not being needed.  No
   monotonicity is assumed -- that is what distinguishes this from the first
   conjunct of monotone-convergence.")

(support 'measurable-fn-liminf
  (forall-guarded '(omega cA cF)
                  (list '(IS-SIGMA-ALGEBRA omega cA)
                        '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(IS-MEASURABLE-FN omega cA (cF n_))))
    '(IS-MEASURABLE-FN omega cA (PTWISE-LIMINF omega cF))))

(warrant! 'measurable-fn-liminf 'reference '(rudin-rca "Thm. 1.14" 29))
(topic!   'measurable-fn-liminf 'analysis)
(gloss!   'measurable-fn-liminf
  "The pointwise lower limit of a sequence of measurable functions is
   measurable.  Rudin Thm. 1.14 (p. 14) proves it for lim sup and notes the
   same holds with inf for sup; Thayer Prop. 2.3 (p. 8) is the special case of
   a sequence that converges.  It is the measurability half of Fatou's lemma
   and is stated separately so a proof of Fatou may cite it.")

(support 'integral-simple-approx
  (forall-guarded '(omega cA f)
                  '((IS-SIGMA-ALGEBRA omega cA) (IS-MEASURABLE-FN omega cA f))
    (forsome-guarded '(cF)
                     (list '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                           (forall-guarded '(n_) '((IN n_ NN))
                             '(IS-SIMPLE-FN omega cA (cF n_)))
                           (forall-guarded '(n_) '((IN n_ NN))
                             '(PTWISE-LE omega (cF n_) (cF (succ n_)))))
      (forall-guarded '(x_) '((IN x_ omega))
        '(= ((PTWISE-SUP omega cF) x_) (f x_))))))

(warrant! 'integral-simple-approx 'reference '(rudin-rca "Thm. 1.17" 30))
(topic!   'integral-simple-approx 'analysis)
(gloss!   'integral-simple-approx
  "Every measurable f : omega -> [0,+inf] is the pointwise supremum of a
   non-decreasing sequence of SIMPLE measurable functions.  Rudin Thm. 1.17
   (p. 15) states exactly this (0 <= s_1 <= s_2 <= ... <= f and s_n(x) -> f(x)
   for every x); Thayer Prop. 2.13 (p. 12) states it with STEP functions
   instead, which is a different class -- see the header.  VNB writes the
   limit as the pointwise supremum, legitimate because the sequence is
   non-decreasing, rather than as a limit, which [0,+inf] does not carry.")

;;; =====================================================================
;;; THE INTEGRAL.  Thayer Thm. 2.7 (pp. 9-10): the unique function on the
;;; measurable f : X -> [0,inf] with properties (1)-(7).  One support apiece.

;;; Notation for the head.  INTEGRAL is seeded from *wff-term-form-heads*
;;; (wff.scm), which registers it as a constant but gives the operator table no
;;; parameter names; declaring them here is what lets the English template read
;;; back, and kind `operator' is what keeps the census filing it with ESUM and
;;; ESUP ("characterized by axiom(s)") rather than with the kernel relations.
(register-operator! 'INTEGRAL 'operator '(omega cA mu f))
(notation! 'INTEGRAL
           'english "the integral of $4 over $1 with respect to the measure $3")

(support 'integral-in
  (forall-guarded '(omega cA mu f)
                  '((IS-MEASURE omega cA mu) (IS-MEASURABLE-FN omega cA f))
    '(IN (INTEGRAL omega cA mu f) RR-POS-STAR)))

(warrant! 'integral-in 'reference '(thayer-measures "Thm. 2.7(1)" 15))
(topic!   'integral-in 'plumbing)
(gloss!   'integral-in
  "The integral of a measurable [0,+inf]-valued function is an element of
   [0,+inf]: it is always defined, and may be +inf.  Thayer Thm. 2.7,
   property (1), p. 9.  This is also the totality half of the characterisation
   -- INTEGRAL is a total operation on measurable functions, so no definedness
   side condition is owed anywhere below.")

(support 'integral-indicator
  (forall-guarded '(omega cA mu a_)
                  '((IS-MEASURE omega cA mu) (IN a_ cA))
    '(= (INTEGRAL omega cA mu (INDICATOR omega a_)) (mu a_))))

(warrant! 'integral-indicator 'reference '(thayer-measures "Thm. 2.7(2)" 16))
(topic!   'integral-indicator 'analysis)
(gloss!   'integral-indicator
  "The integral of the indicator function of a measurable set is the measure
   of that set.  Thayer Thm. 2.7, property (2), p. 10; Rudin's Def. 1.23
   (p. 19) makes the same equation the base case of his construction.  This is
   the only clause of the characterisation that mentions mu at all, and so the
   only one that ties the integral to the measure.")

(support 'integral-infinite-on-null
  (forall-guarded '(omega cA mu a_)
                  '((IS-MEASURE omega cA mu) (IN a_ cA) (= (mu a_) 0))
    '(= (INTEGRAL omega cA mu
          (PTWISE-SCALE omega POS-INF (INDICATOR omega a_)))
        0)))

(warrant! 'integral-infinite-on-null 'reference '(thayer-measures "Thm. 2.7(3)" 16))
(topic!   'integral-infinite-on-null 'analysis)
(gloss!   'integral-infinite-on-null
  "The function that is +inf on a null set and 0 off it integrates to 0.
   Thayer Thm. 2.7, property (3), p. 10.  This is the clause that fixes the
   0 * inf = 0 convention at the level of the integral rather than of the
   arithmetic, and it is why extended-arith.scm defines etimes(0, POS-INF) as
   0 rather than leaving the product undefined.")

(support 'integral-additive
  (forall-guarded '(omega cA mu f g)
                  '((IS-MEASURE omega cA mu)
                    (IS-MEASURABLE-FN omega cA f)
                    (IS-MEASURABLE-FN omega cA g))
    '(= (INTEGRAL omega cA mu (PTWISE-EPLUS omega f g))
        (eplus (INTEGRAL omega cA mu f) (INTEGRAL omega cA mu g)))))

(warrant! 'integral-additive 'reference '(thayer-measures "Thm. 2.7(4)" 16))
(topic!   'integral-additive 'analysis)
(gloss!   'integral-additive
  "The integral of a sum of two measurable [0,+inf]-valued functions is the
   sum of the integrals.  Thayer Thm. 2.7, property (4), p. 10.  Rudin's
   Thm. 1.27 (p. 22) is the countable version, of which this is the two-term
   case; Rudin's linearity theorem 1.32 (p. 25) is a different statement,
   about complex L^1 functions, which VNB cannot state because it has no
   signed or complex integral.")

(support 'integral-homogeneous
  (forall-guarded '(omega cA mu f c)
                  '((IS-MEASURE omega cA mu)
                    (IS-MEASURABLE-FN omega cA f)
                    (IN c RR)
                    (<= 0 c))
    '(= (INTEGRAL omega cA mu (PTWISE-SCALE omega c f))
        (etimes c (INTEGRAL omega cA mu f)))))

(warrant! 'integral-homogeneous 'reference '(thayer-measures "Thm. 2.7(5)" 16))
(topic!   'integral-homogeneous 'analysis)
(gloss!   'integral-homogeneous
  "Positive homogeneity: a nonnegative REAL scalar comes out of the integral.
   Thayer Thm. 2.7, property (5), p. 10, whose alpha ranges over [0,inf), i.e.
   is finite -- VNB carries that restriction as the two hypotheses c in RR and
   0 <= c.  Rudin Prop. 1.24(c) (p. 20) is the same statement.  Together with
   integral-additive and integral-indicator this fixes the integral on every
   simple function.")

(support 'integral-monotone
  (forall-guarded '(omega cA mu f g)
                  '((IS-MEASURE omega cA mu)
                    (IS-MEASURABLE-FN omega cA f)
                    (IS-MEASURABLE-FN omega cA g)
                    (PTWISE-LE omega f g))
    '(<= (INTEGRAL omega cA mu f) (INTEGRAL omega cA mu g))))

(warrant! 'integral-monotone 'reference '(thayer-measures "Thm. 2.7(6)" 16))
(topic!   'integral-monotone 'inequalities)
(gloss!   'integral-monotone
  "The integral is monotone: f <= g pointwise gives integral f <= integral g.
   Thayer Thm. 2.7, property (6), p. 10; Rudin Prop. 1.24(a) (p. 19).  Both
   sources leave the pointwise ordering implicit in the notation f <= g; VNB
   spells it as PTWISE-LE over the ambient omega.")

(support 'integral-sup-of-simple
  (forall-guarded '(omega cA mu f)
                  '((IS-MEASURE omega cA mu) (IS-MEASURABLE-FN omega cA f))
    '(= (INTEGRAL omega cA mu f)
        (ESUP (SEP y_ RR-POS-STAR
                (FORSOME s_
                  (AND (IS-SIMPLE-FN omega cA s_)
                       (AND (PTWISE-LE omega s_ f)
                            (= y_ (INTEGRAL omega cA mu s_))))))))))

(warrant! 'integral-sup-of-simple 'reference '(rudin-rca "Def. 1.23" 34))
(topic!   'integral-sup-of-simple 'analysis)
(gloss!   'integral-sup-of-simple
  "The integral of f is the supremum of the integrals of the simple measurable
   functions below f.  In Rudin (Def. 1.23, p. 19) this IS the definition; in
   VNB it is a THEOREM, because the integral is characterised by Thayer's
   Thm. 2.7 instead of constructed.  So this statement is the bridge between
   the two treatments -- it says VNB's characterised operator is Rudin's
   constructed one -- and it is the reason IS-SIMPLE-FN follows Rudin's
   finite-range definition rather than Thayer's countable-range step
   functions.")

;;; =====================================================================
;;; THE CONVERGENCE THEOREMS.

(support 'monotone-convergence
  (forall-guarded '(omega cA mu cF)
                  (list '(IS-MEASURE omega cA mu)
                        '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(IS-MEASURABLE-FN omega cA (cF n_)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(PTWISE-LE omega (cF n_) (cF (succ n_)))))
    '(AND (IS-MEASURABLE-FN omega cA (PTWISE-SUP omega cF))
          (= (INTEGRAL omega cA mu (PTWISE-SUP omega cF))
             (ESUP (IMAGE (VNB-LAMBDA n_ NN (INTEGRAL omega cA mu (cF n_)))
                          NN))))))

(warrant! 'monotone-convergence 'reference '(thayer-measures "Prop. 2.16" 20))
(topic!   'monotone-convergence 'analysis)
(gloss!   'monotone-convergence
  "Lebesgue's monotone convergence theorem: for a non-decreasing sequence of
   measurable [0,+inf]-valued functions, the pointwise supremum is measurable
   and its integral is the supremum of the integrals.  Thayer Prop. 2.16
   (p. 14), and property (7) of Thm. 2.7 (p. 10), which states it with sup on
   both sides exactly as here; Rudin Thm. 1.26 (p. 21) states it with limits.
   VNB follows Thayer's sup form -- the sequences are monotone, so the two
   agree, and [0,+inf] has ESUP but no limit.")

(support 'fatou
  (forall-guarded '(omega cA mu cF)
                  (list '(IS-MEASURE omega cA mu)
                        '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(IS-MEASURABLE-FN omega cA (cF n_))))
    '(AND (IS-MEASURABLE-FN omega cA (PTWISE-LIMINF omega cF))
          (<= (INTEGRAL omega cA mu (PTWISE-LIMINF omega cF))
              (ELIMINF (VNB-LAMBDA n_ NN
                         (INTEGRAL omega cA mu (cF n_))))))))

(warrant! 'fatou 'reference '(thayer-measures "Thm. 2.26" 23))
(topic!   'fatou 'analysis)
(gloss!   'fatou
  "Fatou's lemma: the integral of the pointwise lower limit is at most the
   lower limit of the integrals, for any sequence of measurable
   [0,+inf]-valued functions.  Thayer Thm. 2.26 (p. 17); Rudin Thm. 1.28
   (p. 23).  Two differences from Thayer, both simplifications: he states the
   hypothesis 'lim inf f_n(x) = g(x) for ALMOST all x' and concludes about
   that g, where VNB names the lower limit outright as PTWISE-LIMINF and
   asserts its measurability as the first conjunct -- there being no
   almost-everywhere vocabulary in the tree yet.  Thayer's Remark 2.27 (p. 18)
   notes that no sigma-finiteness or integrability is needed, and none is
   assumed here.")

(support 'dominated-convergence
  (forall-guarded '(omega cA mu cF f g)
                  (list '(IS-MEASURE omega cA mu)
                        '(IN cF (FUN NN (FUN omega RR-POS-STAR)))
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(IS-MEASURABLE-FN omega cA (cF n_)))
                        '(IS-MEASURABLE-FN omega cA f)
                        '(IS-MEASURABLE-FN omega cA g)
                        (forall-guarded '(n_) '((IN n_ NN))
                          '(PTWISE-LE omega (cF n_) g))
                        '(IN (INTEGRAL omega cA mu g) RR)
                        (forall-guarded '(x_) '((IN x_ omega))
                          '(ECONVERGES-TO (VNB-LAMBDA n_ NN ((cF n_) x_))
                                          (f x_))))
    '(ECONVERGES-TO (VNB-LAMBDA n_ NN (INTEGRAL omega cA mu (cF n_)))
                    (INTEGRAL omega cA mu f))))

(warrant! 'dominated-convergence 'reference '(thayer-measures "Prop. 2.28" 24))
(topic!   'dominated-convergence 'analysis)
(gloss!   'dominated-convergence
  "Lebesgue's dominated convergence theorem: if measurable f_k converge
   pointwise to f and are all dominated by a measurable g of FINITE integral,
   then the integrals of the f_k converge to the integral of f.  Thayer
   Prop. 2.28 (p. 18); Rudin Thm. 1.34 (p. 26).  VNB's statement is the
   [0,+inf]-valued one and differs from both sources in three recorded ways.
   (i) Both state it for real- or complex-valued integrable functions, with
   |f_k| <= g; with values in [0,+inf] the absolute value is the function
   itself, so domination is PTWISE-LE.  (ii) Both conclude the stronger
   'integral of |f - f_k| tends to 0', which needs a signed integral VNB does
   not have; VNB concludes only the convergence of the integrals.  (iii) Both
   allow the hypotheses to hold almost everywhere, VNB requires them
   everywhere, there being no almost-everywhere vocabulary yet.  Finiteness of
   the dominating integral is written 'INTEGRAL(...) in RR', RR being exactly
   the finite part of [0,+inf].")

;;; -----------------------------------------------------------------------
;;; NOT STATED, and why.
;;;
;;;   * ALMOST EVERYWHERE.  Thayer Prop. 2.9 / 2.10 (p. 10) and the whole of
;;;     his Sec. 2.4, and every "a.e." hypothesis in the convergence theorems
;;;     above.  It wants one predicate (a conull set) and would let the three
;;;     convergence statements be given in their source form.  It is the first
;;;     thing to add to this file.
;;;   * THE SIGNED AND COMPLEX INTEGRAL (Thayer Def. 2.12, p. 11; Rudin
;;;     Def. 1.30-1.31, p. 24), and with it Rudin's linearity Thm. 1.32
;;;     (p. 25) and the full form of dominated convergence.  It needs the
;;;     positive and negative parts of a function, hence an order on RR-STAR rather
;;;     than only on RR-POS-STAR.
;;;   * THE L^p SPACES and Holder/Minkowski (Thayer Props. 2.18-2.19, p. 15;
;;;     Def. 2.22, p. 16).  They need the signed integral and a quotient by
;;;     equality a.e.
;;;   * INTEGRATION OVER A SUBSET (Thayer Def. 2.11, p. 11), i.e. the
;;;     indefinite integral, and Rudin Thm. 1.29 (p. 23), that it is a measure.
;;;     Both are one line each once "almost everywhere" is in place, and the
;;;     second is the cleanest first proof target in this file.
;;;   * THE CHANGE OF VARIABLES formula (Thayer Prop. 2.32, p. 19), which needs
;;;     the push-forward measure -- see the corresponding note in measure.scm.
