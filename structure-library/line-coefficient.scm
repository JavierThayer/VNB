;;; geo-vocab.scm -- the coefficient of a vector on a line (for the seed functional of the geometric Hahn-Banach,
;;; TB-2a).  Vocabulary only.  Agent DUAL-FIX, 2026-10-26 (NEW DEFINITION, the user's to confirm).
;;; DESTINATION: structure-library/line-coefficient.scm.  Library: analysis (LINE: linear-functional.scm).
;;;
;;;   LINE-COEF(m, v, u)   the real c with u = c.v (a description; it denotes when u is on LINE(m, v) and v /= 0)

(def-functoid 'LINE-COEF '(m v u)
  '(IOTA lnt_ (AND (IN lnt_ RR) (= u ((ACT m) lnt_ v)))))

(notation! 'LINE-COEF 'kind 'functoid 'arity 3
           'english "the coefficient of $3 on the line through $2")

;;;   SUMSET(m, a, p)      a + p = { x in VEC m : x - z in a for some z in p }   (NEW DEFINITION)
(def-functoid 'SUMSET '(m a p)
  '(SEP smx_ (VEC m) (FORSOME smz_ (AND (IN smz_ p) (IN ((VADD m) smx_ ((ACT m) (- 1) smz_)) a)))))
(notation! 'SUMSET 'kind 'functoid 'arity 3
           'english "the sum set $2 + $3 in $1")
