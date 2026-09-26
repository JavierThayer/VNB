;;; path-integral.scm -- THE VOCABULARY OF THE INTEGRAL ALONG A PATH.
;;; DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/pw-antiderivative-laws.scm, cc-int-laws.scm and
;;; road-laws.scm.
;;;
;;; THE SPECIFICATION is docs/paths-and-line-integrals-2026-09-21.md, sections
;;; 3.2, 3.3 and 3.4 AS REWRITTEN on the evening of 2026-09-21, with the four
;;; decisions of section 4 and the three of section 5.  The sources are the
;;; user's notes ~/docs/complex-analysis.pdf section 3.1 -- equation (44)
;;; defines the integral of a CC-valued function of a real variable
;;; COMPONENTWISE -- and Dieudonne, Foundations of Modern Analysis, 8.7 (the
;;; primitive with an exceptional set) and 9.6 (path, loop, road, circuit).
;;;
;;;     IS-PW-CONTINUOUS-ON(phi, a, b)      phi, a function ON [a,b], is
;;;                                         continuous off a finite partition
;;;     IS-PW-ANTIDERIVATIVE(F, phi, a, b)  F, a function ON [a,b], is continuous
;;;                                         there and has derivative phi(t) at
;;;                                         every t interior to a piece
;;;     PW-INT(phi, a, b)                   F(b) - F(a) for any such F
;;;     CC-INT(phi, a, b)                   equation (44), componentwise
;;;     IS-PATH(gamma, a, b)                Dieudonne 9.6
;;;     IS-ROAD(gamma, dgamma, a, b)        Dieudonne 9.6, dgamma EXPLICIT
;;;     TRACE(gamma, a, b)                  the image of the parameter interval
;;;     LINE-INT(f, gamma, dgamma, a, b)    the integral of f(gamma(t))gamma'(t)
;;;
;;; ---------------------------------------------------------------------
;;; THE RULE OF THE DAY (the user, 2026-09-21): A FUNCTION LIVES ON ITS
;;; INTERVAL.  Every function argument below is a member of FUN(CCINT(a,b), _),
;;; never a member of FUN(RR, _) with a and b as parameters.  In this system a
;;; member of FUN(A,B) is defined EXACTLY on A, so the two are DIFFERENT
;;; statements, and the notes and Dieudonne both write the first.  The real
;;; calculus this rests on was restated for functions on [a,b] in
;;; structure-library/interval-calculus.scm (OOINT, IS-CONTINUOUS-ON,
;;; HAS-DERIV-AT) and theorem-library/interval-mvt.scm (Rolle, the two mean
;;; value theorems, the three bounds).  The abandoned draft
;;; archive/2026-09-21-stopped-14b/pw-integral.scm used the total-function
;;; convention and is NOT the source of anything here.
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT CHECKS, against CLAUDE.md's species of false or
;;; underdetermined statement.  Each one was made before any proof was written.
;;;
;;; (1) EVERY INDEX IS TYPED, AND `succ' IS APPLIED ONLY ON NN.  The partition
;;;     is IS-PARTITION(p, n, a, b) (structure-library/regulated.scm), which
;;;     carries (IN n NN), (<= 1 n) and (IN p (FUN NN RR)); the index binder
;;;     `pai_' is guarded by (IN pai_ (INTERVAL 0 pan_)), and INTERVAL is a SEP
;;;     over NN, so `(SUCC pai_)' is applied to a natural.  `succ' off NN is
;;;     uninterpreted; nothing below applies it anywhere else.
;;;
;;; (2) NO STRICT `=' IS ASSERTED OF A TERM THAT MIGHT NOT DENOTE.  The two
;;;     definite descriptions, PW-INT and (through it) CC-INT, are IOTA terms;
;;;     an IOTA is NEVER certified defined (CLAUDE.md, the LUTINS rule), so a
;;;     law of the form `PW-INT(phi,a,b) = t' asserts its definedness.  EVERY
;;;     law proved about PW-INT is therefore stated UNDER THE HYPOTHESIS that a
;;;     PW-antiderivative exists -- `pw-int-value' takes an
;;;     IS-PW-ANTIDERIVATIVE, `pw-int-in-rr' takes one too -- exactly as
;;;     theorem-library/c-int.scm states the laws of C-INT.  The IOTA is simply
;;;     undefined where phi has no piecewise antiderivative, which is the
;;;     tree's normal treatment of a partial function.
;;;
;;; (3) PHI'S VALUES AT THE PARTITION POINTS DO NOT MATTER, AND ARE NEVER USED.
;;;     The inner universal is guarded by the STRICT inequalities
;;;     `pap_(pai_) < pat_' and `pat_ < pap_(SUCC pai_)', so no t is ever a
;;;     partition point, and a and b are partition points by IS-PARTITION's own
;;;     `p(0) = a', `p(n) = b' (decision 4.2 of the design note: the endpoints
;;;     belong to the exceptional set).  No derivative is taken at an endpoint,
;;;     so no one-sided derivative is needed anywhere.  Two functions phi that
;;;     differ only at partition points have the same piecewise
;;;     antiderivatives: `pw-antiderivative-phi-off-partition' is that fact.
;;;
;;; (4) PHI IS STILL TYPED ON ALL OF [a,b].  The design note keeps phi in
;;;     FUN(CCINT(a,b), RR) "to keep phi simple"; the alternative -- a function
;;;     whose domain is [a,b] minus a finite set -- would make the domain
;;;     depend on the partition, and the partition is existentially quantified.
;;;     The values at the partition points are then arbitrary, which (3) says
;;;     is harmless.
;;;
;;; (5) THE EMPTY AND DEGENERATE CASES.  Every predicate here carries `a < b'
;;;     (it is already a conjunct of IS-PARTITION), so CCINT(a,b) is inhabited
;;;     and OOINT(a,b) is non-empty.  Nothing is vacuously true.  IS-PATH does
;;;     NOT state Dieudonne's "not reduced to a point": `a < b' excludes the
;;;     degenerate PARAMETER interval, and nothing below needs the image to have
;;;     more than one point.
;;;
;;; (6) `F' AND `f' ARE ONE SYMBOL.  Both the VNB reader and MIT Scheme fold to
;;;     lower case, so the notes' F and f would be the same variable.  The
;;;     parameters are spelled `pwf_' (the primitive) and `pphi_' (the
;;;     integrand); the path and its derivative are `pgam' and `dgam'; the
;;;     integrand of a line integral is `pf'.
;;;
;;; (7) NO BINDER FOLDS ONTO A CLASS NAME OR AN ACCESSOR.  The internal binders
;;;     are `pav_', `paw_', `pax_', `pat_', `pan_', `pap_', `pai_'.  None folds
;;;     onto NN ZZ QQ RR CC ORD SET EMPTY-SET POS-INF NEG-INF RR-STAR
;;;     RR-POS-STAR, onto an accessor (CARR PTS DIST IDEN ADD MUL NEG ZERO ONE
;;;     FNRM), or onto a name a predicate body or a driver in the cone
;;;     instantiates at (`x_', `y_', `t_', `r_', `z', `p', `tv_' are all in use
;;;     elsewhere and are all avoided).
;;;
;;; (8) THE COMPOSITE INTEGRAND OF A LINE INTEGRAL, t |-> f(gamma(t))*dgamma(t),
;;;     IS A VNB-LAMBDA OVER CCINT(a,b), and its TYPING needs gamma(t) to lie
;;;     in the domain of f.  That is NOT a condition of the definition -- the
;;;     definition is a term and may fail to denote -- it is a HYPOTHESIS of
;;;     every law about LINE-INT, written `SUBSET (TRACE gamma a b) D' for f in
;;;     FUN(D, CC).  `line-int-integrand-in-fun' is that typing.
;;;
;;; ---------------------------------------------------------------------
;;; WHAT IS OMITTED FROM IS-ROAD, AND WHY IT IS RECORDED HERE.
;;;
;;; Decision 5.3 of the design note reads "piecewise continuity of dgamma WITH
;;; ONE-SIDED LIMITS AT THE PARTITION POINTS".  The one-sided limits are NOT a
;;; conjunct below.  The reason is that the library's IS-RIGHT-LIMIT and
;;; IS-LEFT-LIMIT (structure-library/regulated.scm) are stated for TOTAL
;;; functions, `f in FUN(RR,RR)', and restating them for a function on [a,b] is
;;; a piece of vocabulary of its own that nothing in this batch consumes: the
;;; one-sided limits are needed only for the EXISTENCE theorem (Dieudonne
;;; 8.7.2 -- a regulated function has a primitive), which is the next batch.
;;; Adding them later STRENGTHENS IS-ROAD, so every theorem proved with the
;;; weaker predicate survives; a theorem that needs them will have to take them
;;; as an extra hypothesis until then.  This is recorded so that the gap is
;;; visible rather than silently absent.
;;;
;;; ---------------------------------------------------------------------
;;; Dependencies: extreme-value.scm (CCINT), regulated.scm (IS-PARTITION),
;;; matrix.scm (INTERVAL), interval-calculus.scm (OOINT, IS-CONTINUOUS-ON,
;;; HAS-DERIV-AT), metric-subspace.scm (SUBSPACE-MS), metric-continuity.scm
;;; (IS-CONTINUOUS-AT), numeric-instances.scm (RR-MS, CC-MS), number-systems
;;; (real-part, imag-part, +i, CC), injection.scm (IMAGE).  Nothing is proven
;;; here.

;;; =======================================================================
;;; 3.2  PIECEWISE CONTINUITY AND THE PRIMITIVE WITH A FINITE EXCEPTIONAL SET
;;; =======================================================================

;;; IS-PW-CONTINUOUS-ON(phi, a, b) -- the INTERVAL form of
;;; IS-PIECEWISE-CONTINUOUS (regulated.scm, Definition 4.3 of calculus.pdf).
;;; The partition predicate is the SAME, IS-PARTITION; what changes is that phi
;;; is a function ON [a,b] and that continuity is taken on the metric SUBSPACE
;;; of the interval, which is what IS-CONTINUOUS-ON means.  The total-function
;;; predicate is NOT reused and NOT retired: twelve results are stated with it.
(def-predicate 'IS-PW-CONTINUOUS-ON '(pphi_ a b)
  (conjuncts->and
    (list '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(IN pphi_ (FUN (CCINT a b) RR))
          '(FORSOME pan_ (FORSOME pap_
             (AND (IS-PARTITION pap_ pan_ a b)
                  (FORALL pai_
                    (IMPLIES (AND (IN pai_ (INTERVAL 0 pan_)) (< pai_ pan_))
                      (FORALL pat_
                        (IMPLIES (AND (IN pat_ (CCINT a b))
                                 (AND (< (pap_ pai_) pat_)
                                      (< pat_ (pap_ (SUCC pai_)))))
                          (IS-CONTINUOUS-AT (SUBSPACE-MS RR-MS (CCINT a b))
                                            RR-MS pphi_ pat_)))))))))))

(notation! 'IS-PW-CONTINUOUS-ON 'kind 'predicate 'arity 3
           'english "$1 is piecewise continuous on the interval [$2, $3]")

;;; IS-PW-ANTIDERIVATIVE(F, phi, a, b) -- Dieudonne 8.7 with the exceptional set
;;; FINITE (decision 4.1) and the endpoints in it (decision 4.2).
(def-predicate 'IS-PW-ANTIDERIVATIVE '(pwf_ pphi_ a b)
  (conjuncts->and
    (list '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(IN pwf_ (FUN (CCINT a b) RR))
          '(IN pphi_ (FUN (CCINT a b) RR))
          '(IS-CONTINUOUS-ON pwf_ (CCINT a b))
          '(FORSOME pan_ (FORSOME pap_
             (AND (IS-PARTITION pap_ pan_ a b)
                  (FORALL pai_
                    (IMPLIES (AND (IN pai_ (INTERVAL 0 pan_)) (< pai_ pan_))
                      (FORALL pat_
                        (IMPLIES (AND (IN pat_ (CCINT a b))
                                 (AND (< (pap_ pai_) pat_)
                                      (< pat_ (pap_ (SUCC pai_)))))
                          (HAS-DERIV-AT pwf_ pat_ (pphi_ pat_))))))))))))

(notation! 'IS-PW-ANTIDERIVATIVE 'kind 'predicate 'arity 4
           'english "$1 is a piecewise antiderivative of $2 on the interval [$3, $4]")

(def-predicate 'IS-PW-ANTIDERIVABLE '(pphi_ a b)
  '(FORSOME paw_ (IS-PW-ANTIDERIVATIVE paw_ pphi_ a b)))

(notation! 'IS-PW-ANTIDERIVABLE 'kind 'predicate 'arity 3
           'english "$1 has a piecewise antiderivative on the interval [$2, $3]")

;;; PW-INT(phi, a, b) = F(b) - F(a) for any piecewise antiderivative F.  Built
;;; exactly as C-INT is (theorem-library/c-int.scm): a definite description
;;; whose body PINS THE VALUE'S MEMBERSHIP with an explicit conjunct, because
;;; IS-PW-ANTIDERIVATIVE says nothing whatever about the value.  Its uniqueness
;;; obligation -- two piecewise antiderivatives of one phi have the same
;;; endpoint difference -- is `pw-antiderivative-endpoint-difference'.
(def-functoid 'PW-INT '(pphi_ a b)
  '(IOTA pav_ (AND (IN pav_ RR)
                   (FORSOME paw_ (AND (IS-PW-ANTIDERIVATIVE paw_ pphi_ a b)
                                      (= pav_ (- (paw_ b) (paw_ a))))))))

(notation! 'PW-INT 'kind 'functoid 'arity 3
           'english "the piecewise integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")

;;; =======================================================================
;;; 3.3  THE INTEGRAL OF A CC-VALUED FUNCTION -- equation (44) of the notes
;;; =======================================================================

;;; CC-INT(phi, a, b) = PW-INT(re o phi, a, b) + PW-INT(im o phi, a, b) * i,
;;; for phi in FUN(CCINT(a,b), CC).  The coordinate maps are the VNB-LAMBDAs
;;; `t |-> real-part(phi(t))' and `t |-> imag-part(phi(t))' over CCINT(a,b),
;;; which is the shape IS-CC-DIFF-AT (structure-library/cc-coords.scm) uses, so
;;; the two developments meet without a transfer.  Written `x + y*i' and not
;;; `x + i*y' to match cc-of-pair-def and cc-re-im-of.
(def-functoid 'CC-INT '(pphi_ a b)
  '(+ (PW-INT (VNB-LAMBDA pat_ (CCINT a b) (real-part (pphi_ pat_))) a b)
      (* (PW-INT (VNB-LAMBDA pat_ (CCINT a b) (imag-part (pphi_ pat_))) a b) +i)))

(notation! 'CC-INT 'kind 'functoid 'arity 3
           'english "the complex integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")

;;; =======================================================================
;;; 3.4  PATHS AND ROADS
;;; =======================================================================

;;; A PATH is a continuous map of the compact interval [a,b] into C
;;; (Dieudonne 9.6).  Continuity is continuity of a map of METRIC SPACES from
;;; the subspace of the line on [a,b] to CC-MS -- the same reading
;;; IS-CONTINUOUS-ON gives for a real-valued function on an interval.
(def-predicate 'IS-PATH '(pgam a b)
  (conjuncts->and
    (list '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(IN pgam (FUN (CCINT a b) CC))
          '(FORALL pax_ (IMPLIES (IN pax_ (CCINT a b))
              (IS-CONTINUOUS-AT (SUBSPACE-MS RR-MS (CCINT a b)) CC-MS pgam pax_))))))

(notation! 'IS-PATH 'kind 'predicate 'arity 3
           'english "$1 is a path on the interval [$2, $3]")

;;; A ROAD is a path that is, coordinatewise, a piecewise antiderivative of a
;;; piecewise continuous dgamma (Dieudonne 9.6 with decisions 5.2 and 5.3).
;;; `dgamma' is an EXPLICIT ARGUMENT, as `L' is in IS-DIFF-AT(f, a, L): the
;;; derivative is not determined at the partition points, so an IOTA-defined
;;; gamma' would be undefined there.
(def-predicate 'IS-ROAD '(pgam dgam a b)
  (conjuncts->and
    (list '(IS-PATH pgam a b)
          '(IN dgam (FUN (CCINT a b) CC))
          '(IS-PW-CONTINUOUS-ON
             (VNB-LAMBDA pat_ (CCINT a b) (real-part (dgam pat_))) a b)
          '(IS-PW-CONTINUOUS-ON
             (VNB-LAMBDA pat_ (CCINT a b) (imag-part (dgam pat_))) a b)
          '(IS-PW-ANTIDERIVATIVE
             (VNB-LAMBDA pat_ (CCINT a b) (real-part (pgam pat_)))
             (VNB-LAMBDA pat_ (CCINT a b) (real-part (dgam pat_))) a b)
          '(IS-PW-ANTIDERIVATIVE
             (VNB-LAMBDA pat_ (CCINT a b) (imag-part (pgam pat_)))
             (VNB-LAMBDA pat_ (CCINT a b) (imag-part (dgam pat_))) a b))))

(notation! 'IS-ROAD 'kind 'predicate 'arity 4
           'english "$1 is a road with derivative $2 on the interval [$3, $4]")

;;; The TRACE of a path: the image of the parameter interval.  A functoid, so
;;; `mac' unfolds it in a goal.
(def-functoid 'TRACE '(pgam a b)
  '(IMAGE pgam (CCINT a b)))

(notation! 'TRACE 'kind 'functoid 'arity 3
           'english "the trace of the path $1 on [$2, $3]")

;;; The integral of f along the road (gamma, dgamma) over [a,b] -- Dieudonne's
;;; definition, decision 4.3.  `f' is a CC-valued function whose domain contains
;;; the trace; the integrand t |-> f(gamma(t)) * dgamma(t) is a map of [a,b]
;;; into CC and CC-INT integrates it componentwise.  The domain condition is a
;;; hypothesis of the LAWS, not of the term: see statement check (8).
(def-functoid 'LINE-INT '(pf pgam dgam a b)
  '(CC-INT (VNB-LAMBDA pat_ (CCINT a b) (* (pf (pgam pat_)) (dgam pat_))) a b))

(notation! 'LINE-INT 'kind 'functoid 'arity 5
           'english "the integral of $1 along the road $2 with derivative $3 from $4 to $5")
