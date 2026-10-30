;;; cvx-vocab.scm -- convex combinations and the convex hull in a real normed vector space
;;; (compact-groups notes, Lemma 1.12).  DEFINITIONS ONLY.  Agent ISOM, 2026-10-26 (the user's
;;; to confirm).
;;;
;;;   CONV-LEVEL(m, E, n)  the convex combinations of n+1 points of E, built one point at a time:
;;;                        level 0 is E; level n+1 is the set of (1 - t) x + t y with x in level n,
;;;                        y in E and 0 <= t <= 1 (def-by-nn-recursion; conv-level-zero /
;;;                        conv-level-succ).  Every finite convex combination of points of E is in
;;;                        some level (peel off the last point and renormalise), and conversely.
;;;   CONV-HULL(m, E)      the union of the levels: the set of finite convex combinations of E.
;;;   CONV-JOIN(m, C, a)   the join of C to the point a: the (1 - t) y + t a, y in C, 0 <= t <= 1.
;;;   IS-TOTALLY-BOUNDED-IN(ms, A)
;;;                        the subset A of the metric space ms is totally bounded: for every r > 0
;;;                        finitely many open r-balls (centres anywhere in the space) cover A.  With
;;;                        the centres in the space rather than in A the notion passes to subsets at
;;;                        once; it is the textbook one (the two versions differ by a factor 2 in r).
;;; A convex combination is written (VADD m)((ACT m)(1 - t, x), (ACT m)(t, y)), the shape of
;;; IS-CONVEX-SUBSET (sip-hilbert-vocab.scm), which reads only VEC, VADD and ACT and so applies to
;;; a NORMED-VECTOR-SPACE as it stands.
;;; BINDERS: cvz_ cvx_ cvy_ cvt_ cvl_ cvm_ cve_ cvn_ cjz_ cjy_ cjt_ cjm_ cjc_ cja_ tbm_ tba_ tbr_ tbf_ tbp_ tbc_.
(def-by-nn-recursion 'CONV-LEVEL '(cvm_ cve_)
  'cve_
  '(cvn_ cvl_)
  '(SEP cvz_ (VEC cvm_) (FORSOME cvx_ (AND (IN cvx_ cvl_) (FORSOME cvy_ (AND (IN cvy_ cve_)
     (FORSOME cvt_ (AND (IN cvt_ RR) (AND (<= 0 cvt_) (AND (<= cvt_ 1)
       (= cvz_ ((VADD cvm_) ((ACT cvm_) (- 1 cvt_) cvx_) ((ACT cvm_) cvt_ cvy_)))))))))))))
(notation! 'CONV-LEVEL 'kind 'functoid 'arity 3 'english "the convex combinations of $3 + 1 points of $2 in $1")
(def-functoid 'CONV-HULL '(cvm_ cve_)
  '(BIG-UNION cvn_ NN (CONV-LEVEL cvm_ cve_ cvn_)))
(notation! 'CONV-HULL 'kind 'functoid 'arity 2 'english "the convex hull of $2 in $1")
(def-functoid 'CONV-JOIN '(cjm_ cjc_ cja_)
  '(SEP cjz_ (VEC cjm_) (FORSOME cjy_ (AND (IN cjy_ cjc_)
     (FORSOME cjt_ (AND (IN cjt_ RR) (AND (<= 0 cjt_) (AND (<= cjt_ 1)
       (= cjz_ ((VADD cjm_) ((ACT cjm_) (- 1 cjt_) cjy_) ((ACT cjm_) cjt_ cja_)))))))))))
(notation! 'CONV-JOIN 'kind 'functoid 'arity 3 'english "the join of $2 to the point $3 in $1")
(def-predicate 'IS-TOTALLY-BOUNDED-IN '(tbm_ tba_)
  '(FORALL tbr_ (IMPLIES (POS-RR tbr_)
     (FORSOME tbf_ (AND (IN (CARD tbf_) NN) (AND (SUBSET tbf_ (PTS tbm_))
       (FORALL tbp_ (IMPLIES (IN tbp_ tba_)
         (FORSOME tbc_ (AND (IN tbc_ tbf_) (< ((DIST tbm_) tbc_ tbp_) tbr_)))))))))))
(notation! 'IS-TOTALLY-BOUNDED-IN 'kind 'predicate 'arity 2 'english "$2 is totally bounded in $1")
