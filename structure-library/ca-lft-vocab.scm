;;; ca-lft-vocab.scm -- THE EXTENDED PLANE AND LINEAR FRACTIONAL TRANSFORMATIONS,
;;; complex-analysis.pdf s. 1.6 (eq. (8), the topology before Lemma 1.16, Def. 1.17, (9), (11)).
;;; DEFINITIONS ONLY.  CA-LFT, 2026-10-19.  Library: complex-analysis.
;;;
;;; REPRESENTATION.  The notes fix it: the extended plane is C u {oo}, oo "a new point", with C a
;;; SUBSET (s. 1.6: "introducing a new point oo"; "We will denote C u {oo} by C-bar").  P (Def. 1.17)
;;; is an ALTERNATIVE view, identified with C-bar setwise through phi of (9); the Riemann sphere
;;; (s. 1.6.4) is a third view.  Neither is the carrier here.
;;;
;;; THE NEW POINT (the user's decision, 2026-10-19).  oo is a FRESH CONSTANT, CC-INF, and what it
;;; is enters as two PRIMITIVE facts, the POS-INF pattern of extended-reals.scm:
;;;     cc-inf-in-set       CC-INF in SET
;;;     cc-inf-not-in-cc    not (CC-INF in CC)
;;; WHAT THE STAMP CLAIMS: that these are part of the meaning of the symbol CC-INF -- a new point,
;;; outside the complex numbers -- and not facts owed an argument; they contribute {} to every bill.
;;; They are consistent: the diagonal set {z in CC : z not in z} satisfies both (the agent's first
;;; version DEFINED CC-INF as that set and proved both facts; the user preferred a fresh symbol,
;;; since points at infinity will come up again and a Russell set is an artificial encoding).  No
;;; proof uses anything about CC-INF beyond these two facts.
;;;
;;;   CC-INF                  the point at infinity
;;;   CC-HAT                  C u {oo}
;;;   CC-HAT-OPENS            the notes' topology: U in it iff U subset C and U open, or U is the
;;;                           complement in C u {oo} of a compact subset of C
;;;   CC-HAT-TOP              the pair [CC-HAT, CC-HAT-OPENS], shaped as a TOP-SPACE
;;;   TOP-CONVERGES-TO(t, f, L)   the sequence f converges to L in the topology of t: every open set
;;;                           containing L contains f(n) for all large n
;;;   LFT(a, b, c, d)         eq. (8) extended to C u {oo}: z |-> (az + b)/(cz + d), oo where the
;;;                           denominator vanishes, and oo |-> a/c (oo when c = 0).  It is a linear
;;;                           fractional transformation when ad - bc /= 0.
;;;   HOMOG-POINT(u1, u2)     phi of (9): the point with homogeneous coordinates (u1, u2), that is
;;;                           u1/u2, read as oo when u2 = 0
;;;   LFTS                    the set of linear fractional transformations of C u {oo}
;;;   LFT-GROUP               [LFTS, composition, identity, inverse], shaped as a GROUP (Cor. 1.19)
;;;   MAT-LFT(S)              L_S of Prop. 1.18: the LFT of the 2-by-2 complex matrix S
;;;   CAYLEY                  the Cayley transform (11), z |-> (z - i)/(z + i)
;;;   UPPER-HALF-PLANE        H+ = {z in C : Im z > 0}
;;;   UNIT-CIRCLE             T = {z in C : |z| = 1}
;;;
;;; QUOTIENTS are written x * recip(y), the form the reader gives "x / y", so a statement typed with `/'
;;; and a body unfolded from here are the same term.
;;;
;;; BINDERS end in a tag nothing else uses (cv_, uh_, kh_, lfz_, ...), for the reason CLAUDE.md gives.
;;;
;;; Load window: after structure-library/complex (CC-MS), metric-subspace (SUBSPACE-MS), the metric
;;; compactness file (IS-COMPACT), top-space, compose, bijection (INVERSE-BIJ), matrix (MAT, ENTRY)
;;; and the CC normed field (basic-rings).

(register-constant! 'CC-INF 'defined-fn)
;;; PRIMITIVE by the user's decision of 2026-10-19 (see THE NEW POINT above).
(fluid-let ((*current-provenance* 'primitive))
  (add-axiom! *library* 'cc-inf-in-set
    '(IN CC-INF SET))
  (add-axiom! *library* 'cc-inf-not-in-cc
    '(NOT (IN CC-INF CC))))
(notation! 'CC-INF 'kind 'constant 'arity 0
           'english "the point at infinity of the extended complex plane")

(def-constant 'CC-HAT
  (list 'cc-hat-def
        '(== CC-HAT (UNION CC (SINGLETON CC-INF)))))
(notation! 'CC-HAT 'kind 'constant 'arity 0
           'english "the extended complex plane C u {oo}")

(def-constant 'CC-HAT-OPENS
  (list 'cc-hat-opens-def
        '(== CC-HAT-OPENS
             (SEP uh_ (POWER CC-HAT)
               (OR (AND (SUBSET uh_ CC) (IS-OPEN CC-MS uh_))
                   (FORSOME kh_ (AND (SUBSET kh_ CC)
                                (AND (IS-COMPACT (SUBSPACE-MS CC-MS kh_))
                                     (= uh_ (DIFFERENCE CC-HAT kh_))))))))))
(notation! 'CC-HAT-OPENS 'kind 'constant 'arity 0
           'english "the open sets of the extended complex plane")

(declare-instance! 'CC-HAT-TOP 'TOP-SPACE 'cc-hat-top-def
  '(CC-HAT CC-HAT-OPENS))
(notation! 'CC-HAT-TOP 'kind 'constant 'arity 0
           'english "the extended complex plane with its topology")

(def-predicate 'TOP-CONVERGES-TO '(t f L)
  '(AND (IN f (FUN NN (PTS t)))
   (AND (IN L (PTS t))
        (FORALL ut_ (IMPLIES (IN ut_ (OPENS t))
          (IMPLIES (IN L ut_)
            (FORSOME nt_ (AND (IN nt_ NN)
              (FORALL mt_ (IMPLIES (IN mt_ NN)
                (IMPLIES (<= nt_ mt_) (IN (f mt_) ut_))))))))))))
(notation! 'TOP-CONVERGES-TO 'english "$2 converges to $3 in the topology of $1")

(def-functoid 'LFT '(a b c d)
  '(VNB-LAMBDA lfz_ CC-HAT
     (IF (= lfz_ CC-INF)
         (IF (= c 0) CC-INF (* a (recip c)))
         (IF (= (+ (* c lfz_) d) 0)
             CC-INF
             (* (+ (* a lfz_) b) (recip (+ (* c lfz_) d)))))))
(notation! 'LFT 'kind 'functoid 'arity 4
           'english "the linear fractional map z |-> ($1 z + $2)/($3 z + $4) of the extended plane")

(def-functoid 'HOMOG-POINT '(u v)
  '(IF (= v 0) CC-INF (* u (recip v))))
(notation! 'HOMOG-POINT 'kind 'functoid 'arity 2
           'english "the point of the extended plane with homogeneous coordinates ($1, $2)")

(def-constant 'LFTS
  (list 'lfts-def
        '(== LFTS
             (SEP lff_ (FUN CC-HAT CC-HAT)
               (FORSOME lfa_ (AND (IN lfa_ CC)
               (FORSOME lfb_ (AND (IN lfb_ CC)
               (FORSOME lfc_ (AND (IN lfc_ CC)
               (FORSOME lfd_ (AND (IN lfd_ CC)
                 (AND (NOT (= (- (* lfa_ lfd_) (* lfb_ lfc_)) 0))
                      (= lff_ (LFT lfa_ lfb_ lfc_ lfd_)))))))))))))))
(notation! 'LFTS 'kind 'constant 'arity 0
           'english "the set of linear fractional transformations of the extended plane")

(declare-instance! 'LFT-GROUP 'GROUP 'lft-group-def
  '(LFTS
    (VNB-LAMBDA (LIST lfg_ lfh_) (CARTESIAN LFTS LFTS) (COMPOSE lfg_ lfh_))
    (ID-FUN CC-HAT)
    (VNB-LAMBDA lfg_ LFTS (INVERSE-BIJ lfg_ CC-HAT CC-HAT))))
(notation! 'LFT-GROUP 'kind 'constant 'arity 0
           'english "the group of linear fractional transformations under composition")

(def-functoid 'MAT-LFT '(S)
  '(LFT (ENTRY S 1 1) (ENTRY S 1 2) (ENTRY S 2 1) (ENTRY S 2 2)))
(notation! 'MAT-LFT 'kind 'functoid 'arity 1
           'english "the linear fractional transformation L_$1 of the 2-by-2 matrix $1")

(def-constant 'CAYLEY
  (list 'cayley-def
        '(== CAYLEY (LFT 1 (- +i) 1 +i))))
(notation! 'CAYLEY 'kind 'constant 'arity 0
           'english "the Cayley transform z |-> (z - i)/(z + i)")

(def-constant 'UPPER-HALF-PLANE
  (list 'upper-half-plane-def
        '(== UPPER-HALF-PLANE (SEP hpz_ CC (< 0 (imag-part hpz_))))))
(notation! 'UPPER-HALF-PLANE 'kind 'constant 'arity 0
           'english "the upper half plane {z : Im z > 0}")

(def-constant 'UNIT-CIRCLE
  (list 'unit-circle-def
        '(== UNIT-CIRCLE (SEP ucz_ CC (= (magnitude ucz_) 1)))))
(notation! 'UNIT-CIRCLE 'kind 'constant 'arity 0
           'english "the unit circle {z : |z| = 1}")
