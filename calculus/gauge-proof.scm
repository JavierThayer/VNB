;;; gauge-proof.scm -- machine proof that the NAMED Euclidean gauge GAUGE(s) is
;;; a genuine degree function (calculus/structure-library/euclidean-ring.scm).
;;; Run:  ./prover calculus/gauge-proof.scm
;;;
;;; is-euclidean-ring-def only asserts a degree function EXISTS.  We named one
;;; with the global Hilbert epsilon, GAUGE(s) = CHOICE(EUCLIDEAN-GAUGES s), and
;;; prove it is sound: when s is a Euclidean ring it really is a valid degree
;;; function.  Same shape as chosen-centre-is-centre
;;; (calculus/finite-ball-subcover-proof.scm): the choice is defined because the
;;; set of valid gauges is inhabited (the iota/epsilon definedness proviso).
;;;
;;;   gauge-is-degree :  IS-EUCLIDEAN-RING(s) =>
;;;                        GAUGE(s) in FUN(A s, NN)  and  HAS-DIV-REMAINDER(s, GAUGE s)
;;;
;;; Proof: a Euclidean ring HAS a gauge (euclidean-ring-has-gauge), which lands
;;; in EUCLIDEAN-GAUGES(s) (gauges-mem-build) -- so the set is inhabited and the
;;; epsilon pick lies in it (choice-axiom); the SEP slices (gauges-in-fun,
;;; gauges-spec) read off the two conjuncts.  The eigenvariable deg_2 is the
;;; witnessing gauge introduced by exists-elimination.

(sp (make-wff '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (AND (IN (GAUGE s) (FUN (A s) NN))
          (HAS-DIV-REMAINDER s (GAUGE s)))))))
(di) (di)                                ; peel FORALL s ; assume IS-EUCLIDEAN-RING(s)
(fact 'euclidean-ring-has-gauge 's)      ; exists deg. deg in FUN(A s,NN) and HAS-DIV-REMAINDER s deg
(ai 1) (ai 1)                            ; eigenvar deg_2 ; deg_2 in FUN ; HAS-DIV-REMAINDER s deg_2
(fact 'gauges-mem-build 's 'deg_2)       ; deg_2 in EUCLIDEAN-GAUGES(s)  (the set is inhabited)
(mac 'GAUGE)                             ; unfold GAUGE(s) -> CHOICE(EUCLIDEAN-GAUGES s) in the goal
(di)                                     ; split the goal conjunction
;; conjunct 1: CHOICE(EUCLIDEAN-GAUGES s) in FUN(A s, NN)
(bc* 'gauges-in-fun ())                  ; -> CHOICE(...) in EUCLIDEAN-GAUGES(s)
(bc* 'choice-axiom ())                   ; -> EUCLIDEAN-GAUGES(s) inhabited
(ew 'deg_2) (ass)                        ;    witnessed by deg_2
;; conjunct 2: HAS-DIV-REMAINDER(s, CHOICE(EUCLIDEAN-GAUGES s))
(bc* 'gauges-spec ())
(bc* 'choice-axiom ())
(ew 'deg_2) (ass)
(qed 'gauge-is-degree)
