;;; product-measure.scm -- PRODUCT SIGMA-ALGEBRAS, SECTIONS, DYNKIN SYSTEMS.
;;; Vocabulary only: no proof, no support.  Agent FUBINI-1, 2026-10-10
;;; (scratchpad/triage/FUBINI-1.md).  The proofs are theorem-library/product-measure.scm
;;; (prefix pms-) and theorem-library/fubini.scm (prefix fub-).
;;;
;;; SOURCE.  Thayer, Construction of Measures, Chapter 3, Sec. 2 (pp. 22-23): the product
;;; sigma-algebra A (x) B (the smallest sigma-algebra on X x Y containing the RECTANGLES
;;; A x B, A in A, B in B), Prop. 3.5 (sections of a product-measurable function),
;;; Def. 3.6 (sigma-finite: IS-SIGMA-FINITE, outer-measure-construction.scm), Thm. 3.7
;;; (Fubini), Def. 3.8 (the product measure).
;;;
;;; WHAT AND WHY.
;;;   * X x Y is CARTESIAN(xs, ys); a point of it is the literal pair (LIST x y), whose
;;;     components are read off by NTH (cartesian-nth, cartesian-pair-eq,
;;;     pair-in-cartesian).  A function on X x Y is a member of FUN(CARTESIAN(xs, ys), _)
;;;     APPLIED TO THE PAIR, f((LIST x y)) -- the form finsum-fubini uses -- never f(x, y):
;;;     the sections below are written with it, so no destructuring lambda is involved.
;;;   * RECTANGLES(xs, cA, ys, cB) is the family { aa x bb : aa in cA, bb in cB }, a SEP
;;;     over POWER(CARTESIAN(xs, ys)) with the two witnesses existential; PRODUCT-SIGMA is
;;;     SIGMA-GENERATED over CARTESIAN(xs, ys) of it.  The sigma-algebras are the
;;;     parameters cA, cB (as in MEASURE-4), the spaces xs, ys (X / x, Y / y fold together).
;;;   * The SECTIONS.  X-SECTION(ys, cs, x) = { y in ys : (x, y) in cs } is the section of
;;;     the set cs at the point x of the FIRST factor (a subset of ys); Y-SECTION(xs, cs, y)
;;;     the section at a point y of the second factor.  FN-X-SECTION(ys, f, x) is the
;;;     function y |-> f((x, y)) on ys, FN-Y-SECTION(xs, f, y) the function x |-> f((x, y)).
;;;   * DYNKIN SYSTEMS (the route to the uniqueness and Fubini arguments; the notes use the
;;;     monotone class theorem over the algebra of finite unions of rectangles -- see the
;;;     header of theorem-library/product-measure.scm for why the pi-lambda route was taken).
;;;     IS-DYNKIN-SYSTEM(omega, dd): omega is a set, dd a family of subsets of omega
;;;     containing omega, closed under PROPER differences (b \ a for a subset b) and under
;;;     the union of a nondecreasing sequence -- the form Fubini's class is checked in.
;;;     IS-PI-SYSTEM(pp): closed under binary intersection.  DYNKIN-GENERATED(omega, cE):
;;;     the intersection of the Dynkin systems over omega containing cE, a SEP over
;;;     POWER(omega) as SIGMA-GENERATED and MONOTONE-CLASS-GENERATED are.
;;;   * FUBINI (end of file): X-SECTION-MEASURE / Y-SECTION-MEASURE (x |-> nu(C_x),
;;;     y |-> mu(C^y)), IS-FUBINI-SET (both measurable, equal integrals),
;;;     X-SECTION-INTEGRAL / Y-SECTION-INTEGRAL (the inner integrals of a function), and
;;;     PRODUCT-MEASURE (Def. 3.8).
;;;
;;; Loads after measure.scm (SIGMA-GENERATED), sigma-algebra.scm, the kernel's CARTESIAN.
;;; ====================================================================

(def-functoid 'RECTANGLES '(xs cA ys cB)
  '(SEP rcr_ (POWER (CARTESIAN xs ys))
     (FORSOME rca_ (AND (IN rca_ cA)
       (FORSOME rcb_ (AND (IN rcb_ cB) (= rcr_ (CARTESIAN rca_ rcb_))))))))

(notation! 'RECTANGLES 'kind 'functoid 'arity 4
           'english "the measurable rectangles of $1 x $3 for $2 and $4")

(def-functoid 'PRODUCT-SIGMA '(xs cA ys cB)
  '(SIGMA-GENERATED (CARTESIAN xs ys) (RECTANGLES xs cA ys cB)))

(notation! 'PRODUCT-SIGMA 'kind 'functoid 'arity 4
           'english "the product sigma-algebra of $2 and $4 on $1 x $3")

(def-functoid 'X-SECTION '(ys cs x)
  '(SEP xsy_ ys (IN (LIST x xsy_) cs)))

(notation! 'X-SECTION 'kind 'functoid 'arity 3
           'english "the section of $2 at the first coordinate $3, a subset of $1")

(def-functoid 'Y-SECTION '(xs cs y)
  '(SEP ysx_ xs (IN (LIST ysx_ y) cs)))

(notation! 'Y-SECTION 'kind 'functoid 'arity 3
           'english "the section of $2 at the second coordinate $3, a subset of $1")

(def-functoid 'FN-X-SECTION '(ys f x)
  '(VNB-LAMBDA fsy_ ys (f (LIST x fsy_))))

(notation! 'FN-X-SECTION 'kind 'functoid 'arity 3
           'english "the function $2 with first argument fixed at $3, on $1")

(def-functoid 'FN-Y-SECTION '(xs f y)
  '(VNB-LAMBDA fsx_ xs (f (LIST fsx_ y))))

(notation! 'FN-Y-SECTION 'kind 'functoid 'arity 3
           'english "the function $2 with second argument fixed at $3, on $1")

(def-predicate 'IS-DYNKIN-SYSTEM '(omega dd)
  (conjuncts->and
    (list
      '(IN omega SET)
      '(SUBSET dd (POWER omega))
      '(IN omega dd)
      '(FORALL dya_ (IMPLIES (IN dya_ dd)
         (FORALL dyb_ (IMPLIES (IN dyb_ dd)
           (IMPLIES (SUBSET dya_ dyb_) (IN (COMPLEMENT-IN dyb_ dya_) dd))))))
      '(FORALL dyf_ (IMPLIES (IN dyf_ (FUN NN dd))
         (IMPLIES (FORALL dyn_ (IMPLIES (IN dyn_ NN) (SUBSET (dyf_ dyn_) (dyf_ (succ dyn_)))))
                  (IN (BIG-UNION dyk_ NN (dyf_ dyk_)) dd)))))))

(notation! 'IS-DYNKIN-SYSTEM 'kind 'predicate 'arity 2
           'english "$2 is a Dynkin system of subsets of $1")

(def-predicate 'IS-PI-SYSTEM '(pp)
  '(FORALL pya_ (IMPLIES (IN pya_ pp)
     (FORALL pyb_ (IMPLIES (IN pyb_ pp) (IN (INTERSECTION pya_ pyb_) pp))))))

(notation! 'IS-PI-SYSTEM 'kind 'predicate 'arity 1
           'english "$1 is closed under binary intersection")

(def-functoid 'DYNKIN-GENERATED '(omega cE)
  '(SEP dga_ (POWER omega)
     (FORALL dgb_
       (IMPLIES (AND (IS-DYNKIN-SYSTEM omega dgb_) (SUBSET cE dgb_))
                (IN dga_ dgb_)))))

(notation! 'DYNKIN-GENERATED 'kind 'functoid 'arity 2
           'english "the Dynkin system of subsets of $1 generated by $2")

;;; ---------------------------------------------------------------------
;;; FUBINI (Thm. 3.7).  For a set cs in the product sigma-algebra, the two functions
;;; whose integrals are the iterated integrals of its indicator:
;;;   X-SECTION-MEASURE(xs, ys, nu, cs) = x |-> nu(X-SECTION(ys, cs, x)) on xs,
;;;   Y-SECTION-MEASURE(xs, ys, mu, cs) = y |-> mu(Y-SECTION(xs, cs, y)) on ys
;;; (the inner integral of the indicator of cs is the measure of the section,
;;; integral-indicator); IS-FUBINI-SET says both are measurable and their integrals
;;; agree -- the conclusion of Thm. 3.7 for the indicator of cs.  For a function f on
;;; xs x ys, the inner integrals:
;;;   X-SECTION-INTEGRAL(xs, ys, cB, nu, f) = x |-> INTEGRAL over ys of y |-> f((x, y)),
;;;   Y-SECTION-INTEGRAL(xs, cA, mu, ys, f) = y |-> INTEGRAL over xs of x |-> f((x, y)).

(def-functoid 'X-SECTION-MEASURE '(xs ys nu cs)
  '(VNB-LAMBDA smx_ xs (nu (X-SECTION ys cs smx_))))

(notation! 'X-SECTION-MEASURE 'kind 'functoid 'arity 4
           'english "the function x |-> $3(the section of $4 at x) on $1")

(def-functoid 'Y-SECTION-MEASURE '(xs ys mu cs)
  '(VNB-LAMBDA smy_ ys (mu (Y-SECTION xs cs smy_))))

(notation! 'Y-SECTION-MEASURE 'kind 'functoid 'arity 4
           'english "the function y |-> $3(the section of $4 at y) on $2")

(def-predicate 'IS-FUBINI-SET '(xs cA mu ys cB nu cs)
  (conjuncts->and
    (list
      '(IS-MEASURABLE-FN xs cA (X-SECTION-MEASURE xs ys nu cs))
      '(IS-MEASURABLE-FN ys cB (Y-SECTION-MEASURE xs ys mu cs))
      '(= (INTEGRAL xs cA mu (X-SECTION-MEASURE xs ys nu cs))
          (INTEGRAL ys cB nu (Y-SECTION-MEASURE xs ys mu cs))))))

(notation! 'IS-FUBINI-SET 'kind 'predicate 'arity 7
           'english "the iterated integrals of the indicator of $7 over $1 x $4 with $3 and $6 exist and agree")

(def-functoid 'X-SECTION-INTEGRAL '(xs ys cB nu f)
  '(VNB-LAMBDA six_ xs (INTEGRAL ys cB nu (FN-X-SECTION ys f six_))))

(notation! 'X-SECTION-INTEGRAL 'kind 'functoid 'arity 5
           'english "the function x |-> the integral over $2 with respect to $4 of $5(x, .), on $1")

(def-functoid 'Y-SECTION-INTEGRAL '(xs cA mu ys f)
  '(VNB-LAMBDA siy_ ys (INTEGRAL xs cA mu (FN-Y-SECTION xs f siy_))))

(notation! 'Y-SECTION-INTEGRAL 'kind 'functoid 'arity 5
           'english "the function y |-> the integral over $1 with respect to $3 of $5(., y), on $4")

;;; ---------------------------------------------------------------------
;;; DEF. 3.8: the product measure, rho(C) = the iterated integral of the indicator of
;;; C, i.e. the integral over xs of x |-> nu(C_x) (for sigma-finite mu, nu the other
;;; order gives the same value: product-measure-symmetric).
(def-functoid 'PRODUCT-MEASURE '(xs cA mu ys cB nu)
  '(VNB-LAMBDA pmc_ (PRODUCT-SIGMA xs cA ys cB) (INTEGRAL xs cA mu (X-SECTION-MEASURE xs ys nu pmc_))))

(notation! 'PRODUCT-MEASURE 'kind 'functoid 'arity 6
           'english "the product of the measures $3 and $6")
