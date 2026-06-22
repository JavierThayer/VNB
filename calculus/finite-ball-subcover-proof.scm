;;; finite-ball-subcover-proof.scm -- machine proof of the centre-extraction
;;; lemma  finite-ball-subcover-r-net  (calculus.pdf Prop 3.12, the step that
;;; closes compact => totally bounded), with the choice of centres made
;;; EXPLICIT via the global Hilbert epsilon.  Run:
;;;   ./prover calculus/finite-ball-subcover-proof.scm
;;;
;;; Background: a member of BALL-COVER(s,r) is stored as the SET B(c,r); the map
;;; x |-> B(x,r) is not injective, so recovering "the centre" needs choice.  We
;;; name it: CENTRES(s,B,r) is the centres of B, CHOICE(CENTRES s B r) picks one
;;; (defined because the set is inhabited -- the iota/epsilon proviso), and
;;; CENTRE-SET(s,r,F) = IMAGE(B |-> CHOICE(CENTRES s B r), F) is the chosen
;;; centre set.  Construction + supporting membership/finiteness lemmas live in
;;; structure-library/compactness.scm.
;;;
;;; Two theorems, both to QED:
;;;
;;;   chosen-centre-is-centre  -- the epsilon choice is SOUND: for a cover ball
;;;     U, CHOICE(CENTRES s U r) is in X(s) and B(.,r) = U.  Proof: U in the
;;;     cover makes CENTRES(s,U,r) inhabited (ball-cover-mem-fwd + centres-mem-
;;;     build), so choice-axiom lands the pick in it, and the CENTRES slices give
;;;     both conjuncts.
;;;
;;;   finite-ball-subcover-r-net -- a finite subcover F gives the finite r-net
;;;     CENTRE-SET(s,r,F).  Finiteness is centre-set-finite; for the r-net
;;;     condition, a point p sits in some cover ball U (open-cover-covers-point),
;;;     whose chosen centre (chosen-centre-is-centre) is in CENTRE-SET
;;;     (centre-set-contains-choice) and within r of p (ball-point-le/ne).
;;;
;;; Forward steps (fact/ai) introduce eigenvariables c_2 (centre of U in the
;;; soundness proof), f_3 (the subcover), u_4 (the cover ball about p); these
;;; names are the deterministic fresh-var numbering for this file run in order.

;;; ===== chosen-centre-is-centre =====
(sp (make-wff
  '(FORALL s (FORALL r (FORALL U
     (IMPLIES (IN U (BALL-COVER s r))
       (AND (IN (CHOICE (CENTRES s U r)) (X s))
            (= (BALL s (CHOICE (CENTRES s U r)) r) U))))))))
(di)
(fact 'ball-cover-mem-fwd 's 'r 'U)          ; exists c. c in X(s) and B(c,r)=U
(ai 1) (ai 1)                                ; eigenvar c_2 ; c_2 in X(s) ; B(c_2,r)=U
(fact 'centres-mem-build 's 'U 'r 'c_2)       ; c_2 in CENTRES(s,U,r)  (witness of inhabited)
(di)                                          ; split the goal conjunction
;; conjunct 1: CHOICE(CENTRES s U r) in X(s)
(bc* 'centres-in-carrier ((b 'u) (r 'r)))     ; -> CHOICE(...) in CENTRES(s,U,r)
(bc* 'choice-axiom ())                        ; -> CENTRES(s,U,r) inhabited
(ew 'c_2) (ass)                               ;    witnessed by c_2
;; conjunct 2: B(s, CHOICE(...), r) = U
(bc* 'centres-ball-eq ())
(bc* 'choice-axiom ())
(ew 'c_2) (ass)
(qed 'chosen-centre-is-centre)

;;; ===== finite-ball-subcover-r-net =====
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IMPLIES (FORSOME F (AND (SUBSET F (BALL-COVER s r))
                           (AND (IN (CARD F) NN) (IS-OPEN-COVER s F))))
         (FORSOME N (AND (IN (CARD N) NN) (IS-R-NET s N (X s) r))))))))))
(di) (di) (di) (di) (di)                      ; peel s,r and move metric/r-cond/exists-F to hyps
(ai 1) (ai 1) (ai 1)                          ; eigenvar f_3 ; subcover, |f_3| in NN, open-cover
(ew '(CENTRE-SET s r f_3))                     ; the r-net = chosen centres of f_3
(di)                                           ; split the goal conjunction
;; conjunct I: |CENTRE-SET(s,r,f_3)| in NN
(bc* 'centre-set-finite ((s 's) (r 'r)))
(ass)
;; conjunct II: IS-R-NET(s, CENTRE-SET(s,r,f_3), X(s), r)
(mac 'IS-R-NET)
(di) (di)                                      ; fix p ; assume p in X(s)
(fact 'open-cover-covers-point 's 'f_3 'p)     ; exists U. U in f_3 and p in U
(ai 1) (ai 1)                                  ; eigenvar u_4 ; u_4 in f_3 ; p in u_4
(fact 'subset-mem-fwd 'f_3 '(BALL-COVER s r) 'u_4)   ; u_4 in BALL-COVER(s,r)
(fact 'chosen-centre-is-centre 's 'r 'u_4)     ; CHOICE(CENTRES s u_4 r): in X(s), B(.,r)=u_4
(ai 1)                                          ; split that conjunction
(ew '(CHOICE (CENTRES s u_4 r)))               ; the witnessing centre near p
(di)                                           ; split: membership ; distance
;; c in CENTRE-SET(s,r,f_3)
(bc* 'centre-set-contains-choice ())
(ass)
;; d(c,p) < r  (split into <= and /=, each forward from the cover ball u_4)
(di)
(fact 'ball-point-le 's '(CHOICE (CENTRES s u_4 r)) 'r 'u_4 'p) (ass)
(fact 'ball-point-ne 's '(CHOICE (CENTRES s u_4 r)) 'r 'u_4 'p) (ass)
(qed 'finite-ball-subcover-r-net)
