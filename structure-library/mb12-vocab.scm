;;; mb12-vocab.scm -- vocabulary for construction-of-measures.pdf Appendix A.3: the
;;; snowflake of a metric (A.9) and the prefix metrics on X^N (A.11-A.16).
;;; DEFINITIONS ONLY.  Agent ISOM (brief M-B1B2), 2026-10-26 (NEW DEFINITIONS, the user's
;;; to confirm).
;;;
;;;   SNOWFLAKE(s, e)
;;;       the points of s with the distance d(x, y)^e (RPOW-STAR), as a two-slot list (the
;;;       shape of BDD-METRIC).  A metric space for 0 < e <= 1 (snowflake-is-metric-space).
;;;
;;; BINDERS: snfs_ snfe_ snfu_ snfv_.  Dependencies: metric-space.scm, rpow (RPOW-STAR).

(def-functoid 'SNOWFLAKE '(snfs_ snfe_)
  '(LIST (PTS snfs_)
         (VNB-LAMBDA (LIST snfu_ snfv_) (CARTESIAN (PTS snfs_) (PTS snfs_))
           (RPOW-STAR ((DIST snfs_) snfu_ snfv_) snfe_))))

(notation! 'SNOWFLAKE 'kind 'functoid 'arity 2
           'english "the metric space $1 with its distance raised to the power $2")

;;;   DISCRETE-MS(X)
;;;       the set X with the discrete metric: d(u, v) = 0 if u = v, 1 otherwise.
;;;   SEQ-SPACE-MS(X)
;;;       X^N = FUN(NN, X) with the notes' metric (414),
;;;          d(x, y) = sum { 2^-k : k >= 1, x_k /= y_k },
;;;       built as PRODUCT-METRIC-W of the constant sequence DISCRETE-MS(X) with the weights
;;;       2^-n (n in NN, the notes' index k = n + 1): the bounded discrete distance is 1/2 for
;;;       distinct points, so the n-th summand is 2^-(n+1) exactly when x_n /= y_n.  Its
;;;       points are PRODUCT-CARRIER, which agrees with FUN(NN, X) (seq-space-pts-iff).
;;; BINDERS: dsx_ dsu_ dsv_ sqx_ sqk_.

(def-functoid 'DISCRETE-MS '(dsx_)
  '(LIST dsx_ (VNB-LAMBDA (LIST dsu_ dsv_) (CARTESIAN dsx_ dsx_) (IF (= dsu_ dsv_) 0 1))))
(notation! 'DISCRETE-MS 'kind 'functoid 'arity 1 'english "$1 with the discrete metric")

(def-functoid 'SEQ-SPACE-MS '(sqx_)
  '(PRODUCT-METRIC-W (VNB-LAMBDA sqk_ NN (DISCRETE-MS sqx_)) (VNB-LAMBDA sqk_ NN (/ 1 (power 2 sqk_)))))
(notation! 'SEQ-SPACE-MS 'kind 'functoid 'arity 1
           'english "the sequences in $1 with the metric sum of 2^-k over the indices where they differ")

;;;   COORD-PERMUTE(X, sg)
;;;       the notes' S_sigma of (417): for a sequence sg of permutations of X, the map of X^N
;;;       sending <x_1, x_2, ...> to <sg_1(x_1), sg_2(x_2), ...>.
;;; BINDERS: cpx_ cpg_ cpw_ cpk_.
(def-functoid 'COORD-PERMUTE '(cpx_ cpg_)
  '(VNB-LAMBDA cpw_ (FUN NN cpx_) (VNB-LAMBDA cpk_ NN ((cpg_ cpk_) (cpw_ cpk_)))))
(notation! 'COORD-PERMUTE 'kind 'functoid 'arity 2
           'english "the coordinatewise permutation of the sequences in $1 by $2")

;;; ---------------------------------------------------------------------------
;;; The weighted prefix ultrametric of (419), Appendix A.3.
;;;
;;;   IS-ULTRAMETRIC(s)
;;;       s is a metric space whose distance satisfies d(x, y) <= max(d(x, z), d(z, y)).
;;;   PREFIX-PROD(a, x, n)
;;;       a(x_0) a(x_1) ... a(x_{n-1}), the product of the weights along the first n
;;;       coordinates of x (1 for n = 0).  Defined by recursion on n (def-by-nn-recursion,
;;;       as SUM-AG and MPOW are).
;;;   AGREE-LENGTH(x, y)
;;;       the notes' m(x, y) for x /= y: the number of leading coordinates on which x and y
;;;       agree, i.e. the least index k with x_k /= y_k (indices from 0; the notes count from
;;;       1, so their z_1 ... z_m are x_0 ... x_{m-1} here).  A definite description; it
;;;       denotes when x /= y are sequences.
;;;   PREFIX-DIST(a, x, y)
;;;       (419): 0 when x = y, else 1 / PREFIX-PROD(a, x, AGREE-LENGTH(x, y)).
;;;   ULTRA-SEQ-MS(X, a)
;;;       (X^N, d_a): the sequences in X with PREFIX-DIST.
;;; BINDERS: ppa_ ppx_ ppn_ ppv_ alx_ aly_ alk_ alj_ pdx_ pdy_ usx_ usa_ usu_ usv_ umx_ umy_ umz_ ums_.
(def-predicate 'IS-ULTRAMETRIC '(ums_)
  '(AND (IS-METRIC-SPACE ums_)
        (FORALL umx_ (IMPLIES (IN umx_ (PTS ums_))
          (FORALL umy_ (IMPLIES (IN umy_ (PTS ums_))
            (FORALL umz_ (IMPLIES (IN umz_ (PTS ums_))
              (<= ((DIST ums_) umx_ umy_) (MAX ((DIST ums_) umx_ umz_) ((DIST ums_) umz_ umy_)))))))))))
(notation! 'IS-ULTRAMETRIC 'kind 'predicate 'arity 1 'english "$1 is an ultrametric space")

(def-by-nn-recursion 'PREFIX-PROD '(ppa_ ppx_)
  1
  '(ppn_ ppv_)
  '(* ppv_ (ppa_ (ppx_ ppn_))))
(notation! 'PREFIX-PROD 'kind 'functoid 'arity 3 'english "the product of $1 along the first $3 coordinates of $2")

(def-functoid 'AGREE-LENGTH '(alx_ aly_)
  '(IOTA alk_ (AND (IN alk_ NN)
                   (AND (NOT (= (alx_ alk_) (aly_ alk_)))
                        (FORALL alj_ (IMPLIES (IN alj_ NN) (IMPLIES (< alj_ alk_) (= (alx_ alj_) (aly_ alj_)))))))))
(notation! 'AGREE-LENGTH 'kind 'functoid 'arity 2 'english "the length of the common prefix of $1 and $2")

(def-functoid 'PREFIX-DIST '(ppa_ pdx_ pdy_)
  '(IF (= pdx_ pdy_) 0 (recip (PREFIX-PROD ppa_ pdx_ (AGREE-LENGTH pdx_ pdy_)))))
(notation! 'PREFIX-DIST 'kind 'functoid 'arity 3 'english "the $1-weighted prefix distance of $2 and $3")

(def-functoid 'ULTRA-SEQ-MS '(usx_ usa_)
  '(LIST (FUN NN usx_)
         (VNB-LAMBDA (LIST usu_ usv_) (CARTESIAN (FUN NN usx_) (FUN NN usx_)) (PREFIX-DIST usa_ usu_ usv_))))
(notation! 'ULTRA-SEQ-MS 'kind 'functoid 'arity 2 'english "the sequences in $1 with the $2-weighted prefix ultrametric")
