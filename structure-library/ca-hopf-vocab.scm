;;; ca-hopf-vocab.scm -- THE HOPF FIBRATION, complex-analysis.pdf s. 1.6.3 ((13)-(16), Prop. 1.22,
;;; Def. 1.23, Cor. 1.24).  DEFINITIONS ONLY.  CA-HOPF, 2026-10-25.  Library: complex-analysis.
;;; Destination: structure-library/ca-hopf-vocab.scm.
;;;
;;; READINGS (settled in the brief).  C^2 is CARTESIAN(CC, CC), its points the pairs [u1, u2];
;;; C x R is CARTESIAN(CC, RR), identified with R^2 x R as the notes do.  A modulus squared is
;;; written |z| |z| (magnitude(z) * magnitude(z)), the form the library's magnitude laws use.
;;;
;;;   CC2-SPHERE              S^3 of (15): the pairs [u1, u2] in C^2 with |u1|^2 + |u2|^2 = 1
;;;   UNIT-SPHERE-CR          S^2 of Prop. 1.22: the pairs [z, r] in C x R with |z|^2 + r^2 = 1
;;;   HOPF-MAP(w)             pi of (16): [2 u1 conj(u2), |u1|^2 - |u2|^2] at w = [u1, u2]
;;;   HOMOG-EQUIV(u, w)       the relation ~ of Def. 1.17: u = z w for some z in C \ {0}
;;;   HOPF-QUOTIENT-MAP       the bijection S^2 -> P of Cor. 1.24, P read through phi (HOMOG-POINT)
;;;                           as C u {oo} (CA-LFT): [z, r] |-> phi(z, 1 - r)
;;;
;;; HOPF-QUOTIENT-MAP is the explicit map: on pi(u) = [2 u1 conj(u2), 1 - 2 |u2|^2] (u on S^3) it
;;; gives phi(2 u1 conj(u2), 2 |u2|^2) = phi(u1, u2), which is how the notes' "pi factors through
;;; a bijection S^2 -> P" is read here.
;;;
;;; BINDERS end in tags nothing else uses (hsw_, hsp_, hez_, hqp_).
;;;
;;; Load window: after structure-library/ca-lft-vocab (CC-HAT, HOMOG-POINT); CARTESIAN, NTH,
;;; magnitude and conjugate are base vocabulary.

(def-constant 'CC2-SPHERE
  (list 'cc2-sphere-def
        '(== CC2-SPHERE
             (SEP hsw_ (CARTESIAN CC CC)
               (= (+ (* (magnitude (NTH 1 hsw_)) (magnitude (NTH 1 hsw_)))
                     (* (magnitude (NTH 2 hsw_)) (magnitude (NTH 2 hsw_))))
                  1)))))
(notation! 'CC2-SPHERE 'kind 'constant 'arity 0
           'english "the unit sphere S^3 of C^2")

(def-constant 'UNIT-SPHERE-CR
  (list 'unit-sphere-cr-def
        '(== UNIT-SPHERE-CR
             (SEP hsp_ (CARTESIAN CC RR)
               (= (+ (* (magnitude (NTH 1 hsp_)) (magnitude (NTH 1 hsp_)))
                     (* (NTH 2 hsp_) (NTH 2 hsp_)))
                  1)))))
(notation! 'UNIT-SPHERE-CR 'kind 'constant 'arity 0
           'english "the unit sphere S^2 of C x R")

(def-functoid 'HOPF-MAP '(w)
  '(LIST (* 2 (* (NTH 1 w) (conjugate (NTH 2 w))))
         (- (* (magnitude (NTH 1 w)) (magnitude (NTH 1 w)))
            (* (magnitude (NTH 2 w)) (magnitude (NTH 2 w))))))
(notation! 'HOPF-MAP 'kind 'functoid 'arity 1
           'english "the Hopf map pi($1) = (2 u1 conj(u2), |u1|^2 - |u2|^2)")

(def-predicate 'HOMOG-EQUIV '(u w)
  '(FORSOME hez_ (AND (IN hez_ CC)
                 (AND (NOT (= hez_ 0))
                      (= u (LIST (* hez_ (NTH 1 w)) (* hez_ (NTH 2 w))))))))
(notation! 'HOMOG-EQUIV 'english "$1 and $2 are proportional homogeneous coordinates")

(def-constant 'HOPF-QUOTIENT-MAP
  (list 'hopf-quotient-map-def
        '(== HOPF-QUOTIENT-MAP
             (VNB-LAMBDA hqp_ UNIT-SPHERE-CR
               (HOMOG-POINT (NTH 1 hqp_) (- 1 (NTH 2 hqp_)))))))
(notation! 'HOPF-QUOTIENT-MAP 'kind 'constant 'arity 0
           'english "the bijection S^2 -> C u {oo} through which the Hopf map factors")
