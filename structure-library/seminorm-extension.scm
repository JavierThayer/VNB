;;; sxt-vocab.scm -- a seminorm on a subspace, and the extension of topological-vector-space.pdf Lemma 4.20,
;;; Eq. (113).  Vocabulary only.  Agent DUAL-FIX, 2026-10-26 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/seminorm-extension.scm.  Library: analysis.
;;; Load window: after the INF vocabulary (RA-BASICS) and structure-library/linear-functional.
;;;
;;;   IS-SEMINORM-ON(m, s, p)        p : s -> RR is a seminorm on the subspace s of the real module m
;;;                                  (nonnegative, subadditive, p(lam.x) = |lam| p(x) for real lam)
;;;   SEMINORM-EXT-SET(m, s, p, q, y)   { p(v) + q(w) : v in s, w in VEC m, y = v + w }
;;;   SEMINORM-EXT(m, s, p, q)       y |-> INF(SEMINORM-EXT-SET(m, s, p, q, y)) on VEC m   (the notes' p~)

(def-predicate 'IS-SEMINORM-ON '(m s p)
  '(AND (IN p (FUN s RR))
   (AND (FORALL snx_ (IMPLIES (IN snx_ s) (<= 0 (p snx_))))
   (AND (FORALL snx_ (IMPLIES (IN snx_ s) (FORALL sny_ (IMPLIES (IN sny_ s)
          (<= (p ((VADD m) snx_ sny_)) (+ (p snx_) (p sny_)))))))
        (FORALL snl_ (IMPLIES (IN snl_ RR) (FORALL snx_ (IMPLIES (IN snx_ s)
          (= (p ((ACT m) snl_ snx_)) (* (abs snl_) (p snx_)))))))))))

(def-functoid 'SEMINORM-EXT-SET '(m s p q y)
  '(SEP sxt_ RR (FORSOME sev_ (AND (IN sev_ s) (FORSOME sew_ (AND (IN sew_ (VEC m))
      (AND (= y ((VADD m) sev_ sew_)) (= sxt_ (+ (p sev_) (q sew_))))))))))

(def-functoid 'SEMINORM-EXT '(m s p q)
  '(VNB-LAMBDA sxy_ (VEC m) (INF (SEMINORM-EXT-SET m s p q sxy_))))

(notation! 'IS-SEMINORM-ON 'kind 'predicate 'arity 3
           'english "$3 is a seminorm on the subspace $2 of $1")
(notation! 'SEMINORM-EXT-SET 'kind 'functoid 'arity 5
           'english "the values $3(v) + $4(w) over the splittings $5 = v + w with v in $2")
(notation! 'SEMINORM-EXT 'kind 'functoid 'arity 4
           'english "the extension of the seminorm $3 on $2 dominated by $4")
