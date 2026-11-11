;;; hc2-vocab.scm -- wave of 2026-11-09/10 (agent HAAR-C2), wired 2026-11-10 from scratchpad/haarc2-1109/hc2-vocab.scm.
;;; Library: analysis.

;;; hc2-vocab.scm -- C(s), the continuous real functions on a metric space s with the supremum norm, as a
;;; REAL NORMED VECTOR SPACE (the 7-slot shape of structure-library/normed-vector-space.scm), for the Haar
;;; integral of a compact metric group (compact-groups notes, Theorem 1.9, in the functional form of th-main
;;; Cor 3.82).  DEFINITIONS ONLY.  Agent HAAR-C2, 2026-11-09 (new definitions, the user's to confirm).
;;; DESTINATION: structure-library/hc2-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/positive-functional (CONT-FNS) and extended-reals-pos (ESUP).
;;;
;;;   CK-NORM(s, f)   ESUP of {|f(x)| : x in PTS s}: the supremum norm.  A real number when s is compact
;;;                   and f continuous (theorem ck-norm-real); 0 on the empty space.
;;;   CK-NVS(s)       [the ring view of RR, CONT-FNS(s), pointwise +, the zero function, pointwise -,
;;;                   pointwise scaling, CK-NORM(s, -)]: the space C(s) of Theorem 1.9's proof.  The
;;;                   pointwise lambdas bind sx_, the binder of CONT-FNS's own laws (rmc-cont-fns-add /
;;;                   -scale) and of IS-POSITIVE-FUNCTIONAL, so that a sum or a multiple in C(s) is literally
;;;                   the term those laws speak of.  A normed vector space when s is compact
;;;                   (ck-nvs-is-normed-vector-space).  The textbook C(X) with the sup norm, real scalars.
;;;
;;; BINDERS: ckp_ cks_ ckf_ ckaf_ ckag_ cknf_ cksr_ cksf_ ckvf_ (and sx_ as said).
(def-functoid 'CK-NORM '(cks_ ckf_)
  '(ESUP (IMAGE (VNB-LAMBDA ckp_ (PTS cks_) (abs (ckf_ ckp_))) (PTS cks_))))
(notation! 'CK-NORM 'kind 'functoid 'arity 2 'english "the supremum norm of $2 on $1"
           'tex "\\lVert $2 \\rVert_{\\infty}")

(def-functoid 'CK-NVS '(cks_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
         (CONT-FNS cks_)
         (VNB-LAMBDA (LIST ckaf_ ckag_) (CARTESIAN (CONT-FNS cks_) (CONT-FNS cks_))
           (VNB-LAMBDA sx_ (PTS cks_) (+ (ckaf_ sx_) (ckag_ sx_))))
         (VNB-LAMBDA sx_ (PTS cks_) 0)
         (VNB-LAMBDA cknf_ (CONT-FNS cks_) (VNB-LAMBDA sx_ (PTS cks_) (- (cknf_ sx_))))
         (VNB-LAMBDA (LIST cksr_ cksf_) (CARTESIAN RR (CONT-FNS cks_))
           (VNB-LAMBDA sx_ (PTS cks_) (* cksr_ (cksf_ sx_))))
         (VNB-LAMBDA ckvf_ (CONT-FNS cks_) (CK-NORM cks_ ckvf_))))
(notation! 'CK-NVS 'kind 'functoid 'arity 1
           'english "the normed space of the continuous real functions on $1 with the supremum norm"
           'tex "C({$1})")
