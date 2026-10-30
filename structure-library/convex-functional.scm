;;; hbc-vocab.scm -- convex functionals (topological-vector-space.pdf Def 2.34) and the positively homogeneous
;;; minorant used to prove Cor 2.36 from the sublinear Hahn-Banach.  Vocabulary only.  Agent DUAL-FIX,
;;; 2026-10-26 (NEW DEFINITIONS, the user's to confirm).  DESTINATION: structure-library/convex-functional.scm.
;;; Library: analysis.  Load window: after the INF vocabulary (RA-BASICS).
;;;
;;;   IS-CONVEX-FUNCTIONAL(m, p)   p : VEC m -> [0, inf) with p(t x + (1 - t) y) <= t p(x) + (1 - t) p(y),
;;;                                0 <= t <= 1 (Def 2.34; m a module over the reals)
;;;   HOMOG-SET(m, p, x)           { r in RR : p(t.x) <= t r for some t > 0 }
;;;   HOMOG-MINORANT(m, p)         x |-> INF(HOMOG-SET(m, p, x)), i.e. inf over t > 0 of p(t.x) / t: the
;;;                                largest positively homogeneous functional below p; it is sublinear when
;;;                                p is convex (homog-minorant-sublinear).

(def-predicate 'IS-CONVEX-FUNCTIONAL '(m p)
  '(AND (IN p (FUN (VEC m) RR))
   (AND (FORALL cfx_ (IMPLIES (IN cfx_ (VEC m)) (<= 0 (p cfx_))))
        (FORALL cfx_ (IMPLIES (IN cfx_ (VEC m)) (FORALL cfy_ (IMPLIES (IN cfy_ (VEC m))
          (FORALL cft_ (IMPLIES (IN cft_ RR) (IMPLIES (<= 0 cft_) (IMPLIES (<= cft_ 1)
            (<= (p ((VADD m) ((ACT m) cft_ cfx_) ((ACT m) (- 1 cft_) cfy_)))
                (+ (* cft_ (p cfx_)) (* (- 1 cft_) (p cfy_)))))))))))))))

(def-functoid 'HOMOG-SET '(m p x)
  '(SEP hmr_ RR (FORSOME hmt_ (AND (IN hmt_ RR) (AND (< 0 hmt_) (<= (p ((ACT m) hmt_ x)) (* hmt_ hmr_)))))))

(def-functoid 'HOMOG-MINORANT '(m p)
  '(VNB-LAMBDA hmx_ (VEC m) (INF (HOMOG-SET m p hmx_))))

(notation! 'IS-CONVEX-FUNCTIONAL 'kind 'predicate 'arity 2
           'english "$2 is a convex functional on $1")
(notation! 'HOMOG-SET 'kind 'functoid 'arity 3
           'english "the reals r with $2(t $3) <= t r for some t > 0")
(notation! 'HOMOG-MINORANT 'kind 'functoid 'arity 2
           'english "the positively homogeneous minorant of $2")
