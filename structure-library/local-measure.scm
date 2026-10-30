;;; local-measure.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-mgvocab.scm.
;;; Library: measure.

;;; mf-mgvocab.scm -- local measures (construction-of-measures.pdf ch. 4, sec. 2.3, Def 4.15 and Def 4.19):
;;; DEFINITIONS ONLY.  Agent M-F (target M-G), 2026-10-29 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/local-measure.scm.  Library: measure.
;;; Load window: after structure-library/measure.scm (IS-MEASURE), RESTRICT-SIGMA, RESTRICT.
;;;
;;; IS-HEREDITARY(ca, cb)               cb is a subset of ca closed under taking members of ca below a member.
;;; IS-LOCAL-MEASURE(omega, ca, cb, rho) Def 4.15: ca a sigma-algebra on omega, cb a hereditary subset of ca,
;;;   rho : cb -> [0, +inf], and for every E in cb the restriction of rho to the relativised sigma-algebra
;;;   RESTRICT-SIGMA(ca, E) = {A in ca : A subset E} is a countably additive measure on E.
;;; IS-LOCALLY-NULL(ca, cb, rho, es)    Def 4.19: es in ca and rho(A n es) = 0 for every A in cb.
;;; IS-SIGMA-UNION-OF(cb, es)           es is the union of a sequence of members of cb (es in "B_sigma").

(def-predicate 'IS-HEREDITARY '(ca cb)
  '(AND (SUBSET cb ca)
        (FORALL hde_ (IMPLIES (IN hde_ cb) (FORALL hdf_ (IMPLIES (IN hdf_ ca) (IMPLIES (SUBSET hdf_ hde_) (IN hdf_ cb))))))))
(notation! 'IS-HEREDITARY 'kind 'predicate 'arity 2
           'english "$2 is a hereditary subset of $1")

(def-predicate 'IS-LOCAL-MEASURE '(omega ca cb rho)
  '(AND (IS-SIGMA-ALGEBRA omega ca)
     (AND (IS-HEREDITARY ca cb)
       (AND (IN rho (FUN cb RR-POS-STAR))
            (FORALL lme_ (IMPLIES (IN lme_ cb)
              (IS-MEASURE lme_ (RESTRICT-SIGMA ca lme_) (RESTRICT rho (RESTRICT-SIGMA ca lme_)))))))))
(notation! 'IS-LOCAL-MEASURE 'kind 'predicate 'arity 4
           'english "$4 is a local countably additive measure on the hereditary subset $3 of the sigma-algebra $2 on $1")

(def-predicate 'IS-LOCALLY-NULL '(ca cb rho es)
  '(AND (IN es ca) (FORALL lna_ (IMPLIES (IN lna_ cb) (= (rho (INTERSECTION lna_ es)) 0)))))
(notation! 'IS-LOCALLY-NULL 'kind 'predicate 'arity 4
           'english "$4 is locally null relative to the local measure $3 on $2 in $1")

(def-predicate 'IS-SIGMA-UNION-OF '(cb es)
  '(FORSOME sug_ (AND (IN sug_ (FUN NN cb)) (= es (BIG-UNION sun_ NN (sug_ sun_))))))
(notation! 'IS-SIGMA-UNION-OF 'kind 'predicate 'arity 2
           'english "$2 is the union of a sequence of members of $1")
