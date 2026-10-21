;;; calc3-vocab.scm -- vocabulary for calculus.pdf chapter 3 (metric topology):
;;; the ACCUMULATION POINT of a set (before Prop 3.10) and the HOMEOMORPHISM
;;; (Cor 3.20), the DENSE subset and the LIMIT ALONG a subset (Prop 3.26).
;;; DEFINITIONS ONLY; the laws are proven in theorem-library/calc3-*.scm.
;;; Agent CALC-3, 2026-10-19 (NEW DEFINITIONS, the user's to confirm).
;;;
;;;   IS-ACCUMULATION-POINT(s, A, x)
;;;       s is a metric space, x a point of s, and every open ball B(x, r) of
;;;       positive radius contains a point of A other than x.  The notes: "An
;;;       element x in X is an accumulation point of A subset X if and only if
;;;       every ball B(x, r) contains an element of A distinct from x."  The tree's
;;;       CLUSTER-POINT is a property of a SEQUENCE, not of a set, hence a new name.
;;;       A subset PTS(s) is NOT a conjunct: it is the theorems' hypothesis, as in
;;;       the notes ("A subset X").  BALL is the OPEN ball (d < r).
;;;
;;;   IS-HOMEOMORPHISM(s, t, f)
;;;       f is a bijection of PTS(s) onto PTS(t), continuous from s to t, whose
;;;       inverse bijection INVERSE-BIJ(f, PTS s, PTS t) is continuous from t to s.
;;;       The metric-continuity.scm header names the notion (a continuous bijection
;;;       with continuous inverse) without defining it.
;;;
;;;   IS-DENSE(s, A)
;;;       s is a metric space, A a subset of its points, and every point of s lies in
;;;       the closure of A.  The notes' "A subset X is a dense subspace" (Prop 3.26);
;;;       the tree had only IS-DENSE-SEQ, the density of the RANGE of a sequence.
;;;
;;;   IS-LIMIT-ALONG(s, t, A, f, x, y)
;;;       s and t are metric spaces, y a point of t, and f(a) tends to y as a tends to
;;;       x through A: for every eps > 0 some delta > 0 has d_t(f(a), y) <= eps for
;;;       every a in A with d_s(x, a) <= delta.  The value of the extension in Prop
;;;       3.26 at x (the notes: "the limit of f(x_k) for a sequence x_k -> x in A,
;;;       independent of the sequence"); stated with epsilon and delta so that no
;;;       sequence has to be chosen to say what the value IS.  x is not required to
;;;       lie in A or in PTS(s); f is applied only at points of A.
;;;
;;; STATEMENT CHECKS.  (1) IS-METRIC-SPACE is a conjunct of each (IS-CONTINUOUS
;;; carries it for IS-HOMEOMORPHISM).  (2) No FORSOME witness is formed outside the body;
;;; no IOTA or CHOICE in any body (INVERSE-BIJ has a CHOICE in its body, but it
;;; is applied only under the BIJECTION conjunct, where inverse-bij-in-fun types it).
;;; (3) BINDERS: apts_ apta_ aptx_ aptr_ apty_, hmes_ hmet_ hmef_, dns_ dna_, and
;;; lmas_ lmat_ lmaa_ lmaf_ lmax_ lmay_ lmae_ lmad_ lmaz_; no other body
;;; or driver in the tree binds an apt?_, hme?_, dns_/dna_ or lma?_ name, and none folds onto a class
;;; name, an accessor or a registered constant.
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, PTS, DIST), metric-topology.scm
;;; (BALL), metric-continuity.scm (IS-CONTINUOUS), bijection.scm (INVERSE-BIJ,
;;; BIJECTION), baire-category.scm (CLOSURE).  Load slot: after
;;; structure-library/baire-category (the latest of these).

(def-predicate 'IS-ACCUMULATION-POINT '(apts_ apta_ aptx_)
  '(AND (IS-METRIC-SPACE apts_)
   (AND (IN aptx_ (PTS apts_))
        (FORALL aptr_ (IMPLIES (POS-RR aptr_)
          (FORSOME apty_ (AND (IN apty_ apta_)
                         (AND (IN apty_ (BALL apts_ aptx_ aptr_))
                              (NOT (= apty_ aptx_))))))))))

(notation! 'IS-ACCUMULATION-POINT 'kind 'predicate 'arity 3
           'english "$3 is an accumulation point of $2 in the metric space $1")

(def-predicate 'IS-HOMEOMORPHISM '(hmes_ hmet_ hmef_)
  '(AND (IN hmef_ (BIJECTION (PTS hmes_) (PTS hmet_)))
   (AND (IS-CONTINUOUS hmes_ hmet_ hmef_)
        (IS-CONTINUOUS hmet_ hmes_ (INVERSE-BIJ hmef_ (PTS hmes_) (PTS hmet_))))))

(notation! 'IS-HOMEOMORPHISM 'kind 'predicate 'arity 3
           'english "$3 is a homeomorphism from $1 onto $2")

(def-predicate 'IS-DENSE '(dns_ dna_)
  '(AND (IS-METRIC-SPACE dns_)
   (AND (SUBSET dna_ (PTS dns_))
        (SUBSET (PTS dns_) (CLOSURE dns_ dna_)))))

(notation! 'IS-DENSE 'kind 'predicate 'arity 2
           'english "$2 is dense in the metric space $1")

(def-predicate 'IS-LIMIT-ALONG '(lmas_ lmat_ lmaa_ lmaf_ lmax_ lmay_)
  '(AND (IS-METRIC-SPACE lmas_)
   (AND (IS-METRIC-SPACE lmat_)
   (AND (IN lmay_ (PTS lmat_))
        (FORALL lmae_ (IMPLIES (POS-RR lmae_)
          (FORSOME lmad_ (AND (POS-RR lmad_)
            (FORALL lmaz_ (IMPLIES (IN lmaz_ lmaa_)
              (IMPLIES (<= ((DIST lmas_) lmax_ lmaz_) lmad_)
                       (<= ((DIST lmat_) (lmaf_ lmaz_) lmay_) lmae_))))))))))))

(notation! 'IS-LIMIT-ALONG 'kind 'predicate 'arity 6
           'english "$6 is the limit of $4(a) as a tends to $5 through $3")
