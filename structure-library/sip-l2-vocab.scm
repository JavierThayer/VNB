;;; sip-l2-vocab.scm -- EQUALITY ALMOST EVERYWHERE as a setoid (SIP-1, 2026-10-18).
;;; Vocabulary only.
;;;
;;; THE DESIGN IS THE USER'S (2026-10-18, scratchpad/triage/SIP-1.md): the spaces of
;;; integrable functions are SETOIDS (structure-library/setoid.scm), with equality almost
;;; everywhere as the relation; the precedent is QUOTIENT(CAUCHY-SETOID(M)) in
;;; metric-completion.scm.
;;;
;;; AE-REL(omega, cA, mu, sf): the pairs (f, g) of members of the class sf that agree off a
;;; null set (IS-NULL-SET, outer-measure-construction.scm: a subset of a measurable set of
;;; measure 0), as an extensional SET of pairs, the shape SETOID's relation slot wants.
;;; AE-SETOID(omega, cA, mu, sf) = [sf, AE-REL(omega, cA, mu, sf)].
;;; The parameter is `sf', not `s' or `S' (one folded symbol, the setoid's own variable).
;;;
;;; LOAD WINDOW: after structure-library/outer-measure-construction (IS-NULL-SET).
;;; Library: measure.

(def-functoid 'AE-REL '(omega cA mu sf)
  '(SEP aep_ (CARTESIAN sf sf)
     (FORSOME aen_ (AND (IS-NULL-SET omega cA mu aen_)
       (FORALL aex_ (IMPLIES (IN aex_ omega)
         (IMPLIES (NOT (IN aex_ aen_)) (= ((NTH 1 aep_) aex_) ((NTH 2 aep_) aex_)))))))))

(def-functoid 'AE-SETOID '(omega cA mu sf)
  '(LIST sf (AE-REL omega cA mu sf)))

(notation! 'AE-REL 'kind 'functoid 'arity 4
           'english "equality almost everywhere on $4 with respect to $3")
(notation! 'AE-SETOID 'kind 'functoid 'arity 4
           'english "$4 modulo equality almost everywhere with respect to $3")

;;; -----------------------------------------------------------------------
;;; REAL L^2: the square-integrable real measurable functions, with the pointwise vector
;;; operations and the form <f, g> = integral of f g (RINTEGRAL, real-integral.scm).  A
;;; SEMI-INNER-PRODUCT-SPACE (theorem-library/sip-c.scm); its null vectors are the functions
;;; vanishing almost everywhere, so its null-vector quotient is its AE quotient.
;;; "Square-integrable" is IS-INTEGRABLE of x |-> f(x) f(x).
(def-functoid 'L2-SET '(omega cA mu)
  '(SEP lf_ (FUN omega RR)
     (AND (IS-REAL-MEASURABLE-FN omega cA lf_)
          (IS-INTEGRABLE omega cA mu (VNB-LAMBDA lx_ omega (* (lf_ lx_) (lf_ lx_)))))))

(def-functoid 'L2-VADD '(omega cA mu)
  '(VNB-LAMBDA (LIST lf_ lg_) (CARTESIAN (L2-SET omega cA mu) (L2-SET omega cA mu))
     (VNB-LAMBDA lx_ omega (+ (lf_ lx_) (lg_ lx_)))))
(def-functoid 'L2-VZERO '(omega)
  '(VNB-LAMBDA lx_ omega 0))
(def-functoid 'L2-VNEG '(omega cA mu)
  '(VNB-LAMBDA lf_ (L2-SET omega cA mu) (VNB-LAMBDA lx_ omega (- (lf_ lx_)))))
(def-functoid 'L2-ACT '(omega cA mu)
  '(VNB-LAMBDA (LIST lr_ lf_) (CARTESIAN RR (L2-SET omega cA mu))
     (VNB-LAMBDA lx_ omega (* lr_ (lf_ lx_)))))
(def-functoid 'L2-RIP '(omega cA mu)
  '(VNB-LAMBDA (LIST lf_ lg_) (CARTESIAN (L2-SET omega cA mu) (L2-SET omega cA mu))
     (RINTEGRAL omega cA mu (VNB-LAMBDA lx_ omega (* (lf_ lx_) (lg_ lx_))))))

(def-functoid 'L2-SPACE '(omega cA mu)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (L2-SET omega cA mu) (L2-VADD omega cA mu)
         (L2-VZERO omega) (L2-VNEG omega cA mu) (L2-ACT omega cA mu) (L2-RIP omega cA mu)))

(notation! 'L2-SET 'kind 'functoid 'arity 3 'english "the square-integrable real functions on $1 with respect to $3")
(notation! 'L2-SPACE 'kind 'functoid 'arity 3 'english "the real L^2 space of $3 on $1")

;;; COMPLEX L^2: pairs (u, v) of real L^2 functions, <(u,v),(u',v')> = <u,u'> + <v,v'>,
;;; J(u, v) = (-v, u) -- the complexification (sip-complex-vocab.scm) of real L^2.  No complex
;;; integral is needed.
(def-functoid 'CL2-SPACE '(omega cA mu)
  '(COMPLEXIFY (L2-SPACE omega cA mu)))
(notation! 'CL2-SPACE 'kind 'functoid 'arity 3 'english "the complex L^2 space of $3 on $1")
