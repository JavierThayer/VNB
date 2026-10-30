;;; l1-dual.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/md/me-du-vocab.scm.
;;; Library: measure.

;;; me-du-vocab.scm -- vocabulary for construction-of-measures.pdf Proposition 2.31 (the dual of L^1), definitions only.
;;; Agent M-D (M-E), worker-02, 2026-10-29 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/l1-dual.scm.  Library: measure.  Load window: after real-integral.scm.
;;;
;;;   L1-SET(omega, ca, mu)            the integrable real functions on omega (functions, not classes mod a.e.).
;;;   IS-BOUNDED-L1-FUNCTIONAL(omega, ca, mu, F, cb)
;;;                                    F : L1-SET -> R is additive, homogeneous, and |F(g)| <= cb ||g||_1 with
;;;                                    ||g||_1 = int |g| dmu; i.e. F is an element of (L^1)* of dual norm at most cb.
;;;                                    The sum and the multiple are written exactly as rintegral-add and
;;;                                    rintegral-scale write them (binder sx_), so those laws apply literally.
;;;   L1-PAIRING(omega, ca, mu, f)     the map (43) of the notes: g |-> int f g dmu, on L1-SET.
(def-functoid 'L1-SET '(omega ca mu)
  '(SEP l1g_ (FUN omega RR) (IS-INTEGRABLE omega ca mu l1g_)))
(notation! 'L1-SET 'kind 'functoid 'arity 3
           'english "the set of integrable real functions on $1 with respect to $3")
(def-predicate 'IS-BOUNDED-L1-FUNCTIONAL '(omega ca mu F cb)
  '(AND (IN F (FUN (L1-SET omega ca mu) RR))
   (AND (IN cb RR)
   (AND (<= 0 cb)
   (AND (FORALL bfx_ (IMPLIES (IN bfx_ (L1-SET omega ca mu)) (FORALL bfy_ (IMPLIES (IN bfy_ (L1-SET omega ca mu))
          (= (F (VNB-LAMBDA sx_ omega (+ (bfx_ sx_) (bfy_ sx_)))) (+ (F bfx_) (F bfy_)))))))
   (AND (FORALL bfr_ (IMPLIES (IN bfr_ RR) (FORALL bfx_ (IMPLIES (IN bfx_ (L1-SET omega ca mu))
          (= (F (VNB-LAMBDA sx_ omega (* bfr_ (bfx_ sx_)))) (* bfr_ (F bfx_)))))))
        (FORALL bfx_ (IMPLIES (IN bfx_ (L1-SET omega ca mu))
          (<= (abs (F bfx_)) (* cb (INTEGRAL omega ca mu (ABS-FN omega bfx_))))))))))))
(notation! 'IS-BOUNDED-L1-FUNCTIONAL 'kind 'predicate 'arity 5
           'english "$4 is a linear functional on L^1($1, $3) of norm at most $5")
(def-functoid 'L1-PAIRING '(omega ca mu f)
  '(VNB-LAMBDA lpg_ (L1-SET omega ca mu) (RINTEGRAL omega ca mu (VNB-LAMBDA sx_ omega (* (f sx_) (lpg_ sx_))))))
(notation! 'L1-PAIRING 'kind 'functoid 'arity 4
           'english "the functional g |-> int $4 g d$3 on L^1($1, $3)")
