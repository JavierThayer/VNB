;;; SINCE 2026-10-04 NOTHING IN THIS FILE IS ASSERTED: the fifteen supports that
;;; characterised the integral are THEOREMS -- six in theorem-library/integral-laws.scm
;;; (M-2), nine in theorem-library/integral-convergence.scm (M-3) -- and INTEGRAL is
;;; DEFINED in structure-library/simple-integral.scm (the supremum of the simple
;;; integrals below f).  The header below is the design record from the time the
;;; integral was characterised: where it says `support' read `theorem', and
;;; RR-POS-STAR now has a sethood fact (`rr-pos-star-is-set').
;;;
;;; integral.scm -- MEASURABLE FUNCTIONS, SIMPLE FUNCTIONS and the INTEGRAL of
;;; a [0,+inf]-valued measurable function, with the three convergence theorems.
;;; Vocabulary plus statements; nothing here is proved (the proofs of six of the
;;; statements are theorem-library/integral-laws.scm).
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
;;; SINCE 2026-10-04 THE INTEGRAL IS DEFINED (decision 4 of the October
;;; roadmap): INTEGRAL is the def-functoid of structure-library/simple-integral.scm
;;; (Rudin Def. 1.23, the supremum of the simple integrals below f), loaded right
;;; after this file, and the supports integral-in, -indicator,
;;; -infinite-on-null, -homogeneous, -monotone and -sup-of-simple below are
;;; THEOREMS of theorem-library/integral-laws.scm, to be retired.  The paragraph
;;; that follows describes the characterisation as it stood until then.
;;;
;;; THE INTEGRAL WAS CHARACTERISED, NOT CONSTRUCTED, and the source does it that
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

;;; measurable-fn-indicator RETIRED 2026-09-18 (rake batch 5b): proven in theorem-library/rake-measure2.scm












;;; =====================================================================
;;; THE INTEGRAL.  Thayer Thm. 2.7 (pp. 9-10): the unique function on the
;;; measurable f : X -> [0,inf] with properties (1)-(7).  One support apiece.

;;; (2026-10-04: INTEGRAL is now DEFINED in structure-library/simple-integral.scm,
;;; whose def-functoid re-registers the head as a functoid with the same
;;; parameters; the registration below only covers the statements of this file.)
;;; Notation for the head.  INTEGRAL is seeded from *wff-term-form-heads*
;;; (wff.scm), which registers it as a constant but gives the operator table no
;;; parameter names; declaring them here is what lets the English template read
;;; back, and kind `operator' is what keeps the census filing it with ESUM and
;;; ESUP ("characterized by axiom(s)") rather than with the kernel relations.
(register-operator! 'INTEGRAL 'operator '(omega cA mu f))
(notation! 'INTEGRAL
           'english "the integral of $4 over $1 with respect to the measure $3")















;;; =====================================================================
;;; THE CONVERGENCE THEOREMS.







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
