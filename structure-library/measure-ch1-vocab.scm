;;; measure-ch1-vocab.scm -- ATOMS OF AN ALGEBRA, FINITE UNIONS, RECTANGLES OF R^n, THE PULLBACK SIGMA-ALGEBRA AND
;;; MEASURE (M-A, wave MAP-1026, 2026-10-26).  DEFINITIONS ONLY; destination structure-library/.
;;; Source: Thayer, Construction of Measures, ch. 1: s. 1 (minimal non-empty element, Prop. 1.2; Prop. 1.4;
;;; rectangles, Cor. 1.6), s. 2.1 (Prop. 1.14), s. 4 (Prop. 1.22).
;;;
;;;   IS-ATOM(cA, a)           a is a minimal non-empty element of cA: a in cA, a non-empty, and every
;;;                            non-empty member of cA contained in a is a (notes: "no non-empty [proper]
;;;                            subset of A is an element of A"; "called atoms")
;;;   ATOMS(cA)                the atoms of cA
;;;   FINITE-UNIONS(omega, cI) the unions of the finite subfamilies of cI (subsets of omega); the empty
;;;                            subfamily gives EMPTY-SET
;;;   IS-INTERVAL(es)          es is an interval of R: a subset of RR with a <= x <= b, a, b in es => x in es
;;;   RN-BOX(n, jj)            the rectangle jj(1) x ... x jj(n) in R^n (a point of R^n is a function on
;;;                            INTERVAL(1, n), rn-vocab.scm)
;;;   RN-RECTANGLES(n)         the rectangles of R^n: RN-BOX(n, jj) with every jj(i) an interval
;;;   PULLBACK-SIGMA(omega, cB, f)      { f^-1(b) : b in cB }, f^-1(b) = {x in omega : f(x) in b}
;;;   PULLBACK-MEASURE(omega, cB, f, nu) the measure f^-1(nu) of Prop. 1.22: f^-1(b) |-> nu(b), read as
;;;                            a |-> nu(f(a)) (for f onto, f(f^-1(b)) = b)
;;;
;;; Library: measure.  Load window: after structure-library/rn-vocab (R^n is FUN(INTERVAL(1, n), RR)),
;;; structure-library/sigma-algebra, structure-library/measure and structure-library/injection (IMAGE); before
;;; theorem-library/measure-ch1-algebras.  Proposed slot: right after theorem-library/push-forward.
;;; No proof, no support.

(def-predicate 'IS-ATOM '(cA a)
  '(AND (IN a cA)
        (AND (NOT (= a EMPTY-SET))
             (FORALL mab_ (IMPLIES (IN mab_ cA)
                            (IMPLIES (SUBSET mab_ a)
                              (IMPLIES (NOT (= mab_ EMPTY-SET)) (= mab_ a))))))))
(notation! 'IS-ATOM 'kind 'predicate 'arity 2
           'english "$2 is an atom (a minimal non-empty element) of $1")

(def-functoid 'ATOMS '(cA)
  '(SEP mat_ cA (IS-ATOM cA mat_)))
(notation! 'ATOMS 'kind 'functoid 'arity 1
           'english "the atoms of $1")

(def-functoid 'FINITE-UNIONS '(omega cI)
  '(SEP mfu_ (POWER omega)
     (FORSOME mff_ (AND (IN mff_ SET)
                     (AND (IN (CARD mff_) NN)
                       (AND (SUBSET mff_ cI)
                            (= mfu_ (BIG-UNION mfw_ mff_ mfw_))))))))
(notation! 'FINITE-UNIONS 'kind 'functoid 'arity 2
           'english "the finite unions of members of $2 (subsets of $1)")

(def-predicate 'IS-INTERVAL '(es)
  '(AND (SUBSET es RR)
        (FORALL mia_ (IMPLIES (IN mia_ es)
          (FORALL mib_ (IMPLIES (IN mib_ es)
            (FORALL mix_ (IMPLIES (IN mix_ RR)
              (IMPLIES (<= mia_ mix_) (IMPLIES (<= mix_ mib_) (IN mix_ es)))))))))))
(notation! 'IS-INTERVAL 'kind 'predicate 'arity 1
           'english "$1 is an interval of real numbers")

(def-functoid 'RN-BOX '(n jj)
  '(SEP mrx_ (FUN (INTERVAL 1 n) RR)
     (FORALL mri_ (IMPLIES (IN mri_ (INTERVAL 1 n)) (IN (mrx_ mri_) (jj mri_))))))
(notation! 'RN-BOX 'kind 'functoid 'arity 2
           'english "the rectangle in R^$1 with sides $2")

(def-functoid 'RN-RECTANGLES '(n)
  '(SEP mrr_ (POWER (FUN (INTERVAL 1 n) RR))
     (FORSOME mrj_ (AND (IN mrj_ (FUN (INTERVAL 1 n) (POWER RR)))
                     (AND (FORALL mri_ (IMPLIES (IN mri_ (INTERVAL 1 n)) (IS-INTERVAL (mrj_ mri_))))
                          (= mrr_ (RN-BOX n mrj_)))))))
(notation! 'RN-RECTANGLES 'kind 'functoid 'arity 1
           'english "the rectangles (cartesian products of intervals) in R^$1")

(def-functoid 'PULLBACK-SIGMA '(omega cB f)
  '(SEP mpa_ (POWER omega)
     (FORSOME mpb_ (AND (IN mpb_ cB) (= mpa_ (SEP mpx_ omega (IN (f mpx_) mpb_)))))))
(notation! 'PULLBACK-SIGMA 'kind 'functoid 'arity 3
           'english "the pullback by $3 of the sigma-algebra $2 to $1")

(def-functoid 'PULLBACK-MEASURE '(omega cB f nu)
  '(VNB-LAMBDA mpm_ (PULLBACK-SIGMA omega cB f) (nu (IMAGE f mpm_))))
(notation! 'PULLBACK-MEASURE 'kind 'functoid 'arity 4
           'english "the pullback by $3 of the measure $4 on $2")
