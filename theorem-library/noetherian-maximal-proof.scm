;;; noetherian-maximal-proof.scm -- the noetherian maximal-element principle,
;;; MACHINE-PROVEN, and its specialisation hb-good-has-maximal (the input that
;;; makes finite-dimensional Hahn-Banach terminate).
;;;
;;;   noetherian-set-has-maximal:  m noetherian, Sigma a nonempty set of
;;;     submodules of VEC(m)  =>  Sigma has a member maximal under inclusion.
;;;   hb-good-has-maximal:  m finite-dimensional => the family of subspaces to
;;;     which f extends norm-preservingly has a maximal element.
;;;
;;; PROVED from the IS-NOETHERIAN chain condition (ascending chain condition)
;;; itself -- NOT warranted.  The standard argument, mechanised: assume no
;;; maximal element; then every element has a strict superset, so dependent
;;; choice (dc-on-nn-pred) builds a strictly ascending chain f : NN -> Sigma;
;;; but ACC forces f(succ k) = f(k) for some k, contradicting strictness.
;;; hb-good-has-maximal specialises this to Sigma = { reachable subspaces },
;;; a separation subset of POWER(VEC m).
;;;
;;; Discharges the former hb-good-has-maximal warrant.  Loads after
;;; hahn-banach-proof (for hb-detach-opt!) and before hahn-banach-full-proof
;;; (which consumes GOOD-SUB / NPE / good-sub-submodule / hb-good-has-maximal).
;;; Modulo a clean foundational core: dc-on-nn-pred (dependent choice) plus
;;; trivial logic/set/typing facts (neq-sym, fun-codomain-superset, nn-le-succ,
;;; nn-succ-closed, fun-apply-type-c) and the obvious reachability bridges.

;;; --- foundational helpers (trivial logic / set theory) ---
;;; neq-sym now lives in structure-library/order-lemmas.scm (loaded early, so the
;;; Smith clearing bricks can fact it); it is registered before this file loads.

(add-to-pss 'fun-codomain-superset
  '(FORALL f (FORALL A (FORALL B (FORALL C
     (IMPLIES (IN f (FUN A B)) (IMPLIES (SUBSET B C) (IN f (FUN A C)))))))))
(warrant! 'fun-codomain-superset 'well-known
  "A function into B is a function into any superset C (fun-codomain-iff + subset-mem).")
(topic! 'fun-codomain-superset 'plumbing)

;; nn-le-succ (k <= succ k) was declared here; moved to order-lemmas.scm
;; 2026-07-10 (a plumbing fact belongs there, not in a proof file, and the
;; span-bricks load before this file and need it).

;;; ====================================================================
;;; noetherian-set-has-maximal
;;; ====================================================================
(sp '(FORALL m (IMPLIES (IS-NOETHERIAN m)
     (FORALL sig (IMPLIES (IN sig SET)
      (IMPLIES (SUBSET sig (POWER (VEC m)))
       (IMPLIES (FORALL t (IMPLIES (IN t sig) (IS-SUBMODULE m t)))
        (IMPLIES (FORSOME t0 (IN t0 sig))
          (FORSOME t (AND (IN t sig)
            (FORALL u (IMPLIES (AND (IN u sig) (SUBSET t u)) (= t u)))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)))   ; m,NOETH,sig,SET,SUBSET,SUBMEM,FORSOME-t0
(define nm-sig (cadr (dc-find (lambda (z) (and ((dc-head? 'SUBSET) z) (equal? (caddr z) '(POWER (VEC m))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? nm-sig z)))))
(define nm-t0 (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) nm-sig))))))
(define SUBMEM (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'is-submodule z)))))
(define MAINgoal (dc-gf))

;;; pbc on the main goal
(pbc)                                                ; assume H=NOT(exists maximal); goal FALSITY
(define Hmax (dc-find (lambda (z) (and ((dc-head? 'NOT) z) (dc-ment? 'subset z) (dc-ment? nm-sig z)))))
(define FALS (dc-gf))

;;; the step set and the dc-on-nn-pred totality hypothesis
(define NXT (list 'VNB-LAMBDA '(LIST kx ux) (list 'CARTESIAN 'NN nm-sig)
                  (list 'SEP 'zz nm-sig '(AND (SUBSET ux zz) (NOT (= zz ux))))))
(define (NXTapp k u) (list NXT k u))
(define (SEPof u) (list 'SEP 'zz nm-sig (list 'AND (list 'SUBSET u 'zz) (list 'NOT (list '= 'zz u)))))
(define TOT
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u nm-sig)
      (list 'FORSOME 'y (list 'AND (list 'IN 'y nm-sig) (list 'IN 'y (NXTapp 'k 'u)))))))))
(cut TOT)
(dc-focus! TOT)
(quietly (lambda () (di)(di)(di)(di)))               ; kk,(IN kk NN),uu,(IN uu sig)
(define totU (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) nm-sig)
                                       (not (equal? (cadr z) nm-t0))))))
(define UU (cadr totU))
(define KK (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) 'NN))))))

;;; ---- prove the totality item: uu (in sig) has a strict superset in sig ----
(pbc)                                                ; Hno=NOT(exists strict superset); goal FALSITY
(define Hno (dc-find (lambda (z) (and ((dc-head? 'NOT) z) (dc-ment? 'zz z)))))
(define MAINEX (cadr Hmax))                          ; the main existential
(define MAXPuu (list 'FORALL 'w (list 'IMPLIES
                  (list 'AND (list 'IN 'w nm-sig) (list 'SUBSET UU 'w)) (list '= UU 'w))))
;; establish MAXP(uu)
(cut MAXPuu)
(quietly (lambda () (di)))                            ; w
(quietly (lambda () (di)))                            ; (AND (IN w sig)(SUBSET uu w))
(dc-split)
(define WW (caddr (dc-find (lambda (z) (and ((dc-head? 'SUBSET) z) (equal? (cadr z) UU))))))
(define MAXPbody (dc-gf))                             ; (= uu w)
(pbc)                                                 ; Hneq=NOT(= uu w); goal FALSITY
(quietly (lambda () (fact 'neq-sym UU WW)))           ; NOT(= w uu)
;; w in NXT(kk,uu)
(cut (list '== (NXTapp KK UU) (SEPof UU)))
(dc-focus! (list '== (NXTapp KK UU) (SEPof UU))) (lam-b) (qrfl)
;; back to the inner FALSITY (the (= uu w) pbc), marked by Hneq
(define Hneq (list 'NOT (list '= UU WW)))
(dc-focus-case! Hneq)
;; WW in NXT(kk,uu): rewrite to SEP membership, then sep-mi
(cut (list 'IN WW (NXTapp KK UU)))
(subst (list '== (NXTapp KK UU) (SEPof UU)))        ; goal (IN WW (SEPof uu))
(sep-mi)
(quietly (lambda () (dc-grind!)))                    ; (IN WW sig); SUBSET uu WW; NOT(= WW uu)
(dc-focus-case! Hneq)
;; produce the strict-superset existential and contradict Hno
(cut (cadr Hno))                                     ; (FORSOME y (AND (IN y sig)(IN y NXT)))
(ew WW)
(quietly (lambda () (dc-grind!)))                    ; (IN WW sig); (IN WW NXT)
(dc-focus-case! Hneq)
(ai Hno)                                             ; not-elim closes inner FALSITY -> (= uu w) proven
;; MAXP(uu) established; contradict Hmax at t=uu
(dc-focus-case! Hno)                                 ; totality FALSITY (marked by Hno)
(cut MAINEX)
(ew UU)
(quietly (lambda () (dc-grind!)))                    ; (IN uu sig); MAXP(uu)
(dc-focus-case! Hno)
(ai Hmax)                                            ; closes totality FALSITY

;;; ====================================================================
;;; chunk C: build the ascending chain, apply ACC, contradict
;;; ====================================================================
(quietly (lambda () (fact 'dc-on-nn-pred nm-sig nm-t0 NXT)))   ; -> FORSOME f (chain)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? nm-t0 z) (dc-ment? 'zz z)))))
(dc-split)                                            ; (IN FF (FUN NN sig)); (= (FF 0) t0); FSTEP
(define FF (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) (list 'FUN 'NN nm-sig)))))))
(define FSTEP (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? FF z) (dc-ment? 'zz z)))))
(quietly (lambda () (fact 'fun-codomain-superset FF 'NN nm-sig '(POWER (VEC m)))))  ; IN FF (FUN NN POWER)

;; CH1: every f(n) is a submodule
(define CH1 (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list 'IS-SUBMODULE 'm (list FF 'n_)))))
(cut CH1)
(quietly (lambda () (di)(di)))
(define NN1 (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) 'NN))))))
(quietly (lambda () (fact 'fun-apply-type-c FF 'NN nm-sig NN1)))   ; (IN (FF n) sig)
(quietly (lambda () (inst+ SUBMEM (list FF NN1))))
(hb-detach-opt! (list 'IN (list FF NN1) nm-sig))
(quietly (lambda () (ass-all)))
(dc-focus-case! Hmax)

;; CH2: the chain is nondecreasing
(define CH2 (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
              (list 'SUBSET (list FF 'n_) (list FF '(succ n_))))))
(cut CH2)
(quietly (lambda () (di)(di)))
(define NN2 (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) 'NN))))))
(define CH2GOAL (dc-gf))
(quietly (lambda () (inst+ FSTEP NN2)))
(hb-detach-opt! (list 'IN NN2 'NN))                   ; (IN (FF(succ n))(NXT n (FF n)))
(cut (list '== (NXTapp NN2 (list FF NN2)) (SEPof (list FF NN2))))
(dc-focus! (list '== (NXTapp NN2 (list FF NN2)) (SEPof (list FF NN2))))
;; NXT's domain is NN x sig: n_ is typed by the di, (FF n_) is not -- same
;; citation as CH1 above, one line earlier than it was needed there.
(quietly (lambda () (fact 'fun-apply-type-c FF 'NN nm-sig NN2)))
(lam-b) (qrfl)
(dc-focus! CH2GOAL)
(cut (list 'IN (list FF (list 'succ NN2)) (SEPof (list FF NN2))))
(subst (list '== (SEPof (list FF NN2)) (NXTapp NN2 (list FF NN2))))
(quietly (lambda () (ass-all)))
(dc-focus! CH2GOAL)
(sep-me (list 'IN (list FF (list 'succ NN2)) (SEPof (list FF NN2))))
(dc-split)
(quietly (lambda () (ass-all)))
(dc-focus-case! Hmax)

;; apply ACC (the chain condition inside IS-NOETHERIAN)
(define NOETH (dc-find (lambda (z) (and ((dc-head? 'IS-NOETHERIAN) z)))))
(mac-h 'IS-NOETHERIAN NOETH)
(dc-split)                                            ; split noetherian AND (BEFORE building CH12)
(define CHAINCOND (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'power z) (dc-ment? 'is-submodule z)))))
(define CH12 (list 'AND CH1 CH2))
(cut CH12) (dc-grind!) (dc-focus-case! Hmax)          ; build CH12 after the last dc-split
(quietly (lambda () (inst+ CHAINCOND FF)))
(hb-detach-opt! (list 'IN FF '(FUN NN (POWER (VEC m)))))
(hb-detach-opt! CH12)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? FF z) (dc-ment? '<= z)))))
(define STABAND (dc-find (lambda (z) (and ((dc-head? 'AND) z) (dc-ment? FF z) (dc-ment? '<= z)))))
(define KSTAB (cadr (cadr STABAND)))
(dc-split)
(define STAB (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? FF z) (dc-ment? '<= z)))))

;; STAB at succ kstab gives f(succ k)=f(k); fstep gives the strict inclusion
(quietly (lambda () (fact 'nn-succ-closed KSTAB)))
(quietly (lambda () (fact 'nn-le-succ KSTAB)))
(quietly (lambda () (inst+ STAB (list 'succ KSTAB))))
(define STABANT (list 'AND (list 'IN (list 'succ KSTAB) 'NN) (list '<= KSTAB (list 'succ KSTAB))))
(cut STABANT) (dc-grind!) (dc-focus-case! Hmax)
(hb-detach-opt! STABANT)                              ; (= (FF(succ k))(FF k))
(define FFk (list FF KSTAB))
(define FFsucc (list FF (list 'succ KSTAB)))
(quietly (lambda () (inst+ FSTEP KSTAB)))
(hb-detach-opt! (list 'IN KSTAB 'NN))
(cut (list '== (NXTapp KSTAB FFk) (SEPof FFk)))
(dc-focus! (list '== (NXTapp KSTAB FFk) (SEPof FFk)))
(quietly (lambda () (fact 'fun-apply-type-c FF 'NN nm-sig KSTAB)))   ; (IN (FF k) sig)
(lam-b) (qrfl)
(dc-focus-case! Hmax)
(cut (list 'IN FFsucc (SEPof FFk)))
(subst (list '== (SEPof FFk) (NXTapp KSTAB FFk)))
(quietly (lambda () (ass-all)))
(dc-focus-case! Hmax)
(sep-me (list 'IN FFsucc (SEPof FFk)))
(dc-split)
(dc-focus-case! Hmax)
(ai (dc-find (lambda (z) (and ((dc-head? 'NOT) z) (dc-ment? FF z) (dc-ment? 'succ z)))))
(qed (quote noetherian-set-has-maximal))
(topic! 'noetherian-set-has-maximal 'analysis)

;;; ====================================================================
;;; vocabulary for the Hahn-Banach reachable family (used by hahn-banach-full)
;;; ====================================================================

;;; NPE(m,s,f,t,g): g is a norm-preserving extension of f to the subspace t
;;; (bound measured against the original ||f||_s = DUAL-NORM-ON(m,s,f)).
(def-predicate 'NPE '(m s f t g)
  (conjuncts->and
   '((IS-SUBMODULE m t)
     (SUBSET s t)
     (IS-LINEAR-FUNCTIONAL-ON m t g)
     (EXTENDS-ON s g f)
     (FORALL w_ (IMPLIES (IN w_ t)
        (<= (abs (g w_)) (* (DUAL-NORM-ON m s f) ((VNRM m) w_))))))))

;;; GOOD-SUB(m,s,f,t): t is reachable -- some g is a norm-preserving extension to t.
(def-predicate 'GOOD-SUB '(m s f t)
  '(FORSOME g_ (NPE m s f t g_)))

(add-to-pss 'good-sub-submodule
  '(FORALL m (FORALL s (FORALL f (FORALL t
     (IMPLIES (GOOD-SUB m s f t) (IS-SUBMODULE m t)))))))
(warrant! 'good-sub-submodule 'reference
  "GOOD-SUB unfolds to NPE, whose first conjunct is IS-SUBMODULE m t.")
(topic! 'good-sub-submodule 'analysis)

;;; ====================================================================
;;; bridge warrants + hb-good-has-maximal (specialise nsm to good subspaces)
;;; ====================================================================
(add-to-pss 'good-sub-self
  '(FORALL m (FORALL s (FORALL f
     (IMPLIES (IS-SUBMODULE m s) (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
       (GOOD-SUB m s f s)))))))
(warrant! 'good-sub-self 'reference
  "f is a norm-preserving extension of itself to s (bound = ||f||_s), so s is reachable.")
(topic! 'good-sub-self 'analysis)

(add-to-pss 'vspace-vec-is-set
  '(FORALL m (IMPLIES (IS-VECTOR-SPACE m) (IN (VEC m) SET))))
(warrant! 'vspace-vec-is-set 'reference
  "The carrier VEC(m) of a vector space (module) is a set.")
(topic! 'vspace-vec-is-set 'analysis)

(add-to-pss 'good-sub-in-power
  '(FORALL m (FORALL s (FORALL f (FORALL t
     (IMPLIES (GOOD-SUB m s f t) (IN t (POWER (VEC m)))))))))
(warrant! 'good-sub-in-power 'reference
  "A reachable t is a submodule, hence a subset of VEC(m), hence in its powerset.")
(topic! 'good-sub-in-power 'analysis)

(sp '(FORALL m (FORALL s (FORALL f
     (IMPLIES (IS-FINITE-DIMENSIONAL m)
      (IMPLIES (IS-SUBMODULE m s)
       (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
         (FORSOME t (AND (GOOD-SUB m s f t)
           (FORALL u (IMPLIES (AND (GOOD-SUB m s f u) (SUBSET t u)) (= t u))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))   ; m,s,f,FINDIM,SUBMODULE,BOUNDED
(define HDgoal (dc-gf))
(mac-h 'IS-FINITE-DIMENSIONAL '(IS-FINITE-DIMENSIONAL m))
(dc-split)                                        ; IS-VECTOR-SPACE m, IS-NOETHERIAN m
(define SIG (list 'SEP 'w_ '(POWER (VEC m)) '(GOOD-SUB m s f w_)))

;; IN SIG SET
(cut (list 'IN SIG 'SET))
(sep-set)                                         ; subgoal (IN (POWER (VEC m)) SET)
(quietly (lambda () (fact 'vspace-vec-is-set 'm)))
(quietly (lambda () (fact 'power-set '(VEC m))))
(quietly (lambda () (ass-all)))
(dc-focus! HDgoal)

;; SUBSET SIG (POWER (VEC m))
(cut (list 'SUBSET SIG '(POWER (VEC m))))
(mac 'subset-def)
(quietly (lambda () (di)(di)))
(define Xm (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) SIG))))))
(sep-me (list 'IN Xm SIG))
(quietly (lambda () (ass-all)))
(dc-focus! HDgoal)

;; forall t in SIG, IS-SUBMODULE m t
(cut (list 'FORALL 't_ (list 'IMPLIES (list 'IN 't_ SIG) (list 'IS-SUBMODULE 'm 't_))))
(quietly (lambda () (di)(di)))
;; `Tm' case-folds to `tm', which is the term-with-holes surface helper
;; (input-context.scm:411).  A top-level (define Tm ...) here silently rebound
;; it to a list for the rest of the session.  Use the file's dc- prefix.
(define dc-tm (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) SIG))))))
(sep-me (list 'IN dc-tm SIG))
(quietly (lambda () (fact 'good-sub-submodule 'm 's 'f dc-tm)))
(quietly (lambda () (ass-all)))
(dc-focus! HDgoal)

;; FORSOME t0 in SIG (t0 = s)
(quietly (lambda () (fact 'good-sub-self 'm 's 'f)))      ; GOOD-SUB(s)
(quietly (lambda () (fact 'good-sub-in-power 'm 's 'f 's)))  ; IN s POWER
(cut (list 'FORSOME 't0 (list 'IN 't0 SIG)))
(ew 's)
(sep-mi)
(quietly (lambda () (ass-all)))
(dc-focus! HDgoal)

;; apply nsm; get a maximal T in SIG
(quietly (lambda () (fact 'noetherian-set-has-maximal 'm SIG)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'sep z) (dc-ment? 'subset z)))))
(dc-split)                                        ; (IN TT2 SIG), MAXSIG
(define TT2 (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) SIG))))))
(define MAXSIG (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'sep z) (dc-ment? '= z)))))
(sep-me (list 'IN TT2 SIG))                       ; GOOD-SUB(TT2), IN TT2 POWER
(dc-focus! HDgoal)
(ew TT2)
(di)                                              ; GOOD-SUB(TT2) ; the maximal FORALL
(quietly (lambda () (ass-all)))                   ; closes GOOD-SUB(TT2)
(set-proof-state-focus! *ps* (car (dc-open-leaves)))
(quietly (lambda () (di)(di)))                    ; u ; (AND (GOOD-SUB u)(SUBSET TT2 u))
(dc-split)
(define Uu (caddr (dc-find (lambda (z) (and ((dc-head? 'SUBSET) z) (equal? (cadr z) TT2))))))
(define MAXBODY (dc-gf))                          ; (= TT2 u)
(quietly (lambda () (fact 'good-sub-in-power 'm 's 'f Uu)))     ; IN u POWER
(cut (list 'IN Uu SIG))
(sep-mi)
(quietly (lambda () (ass-all)))
(dc-focus! MAXBODY)
(cut (list 'AND (list 'IN Uu SIG) (list 'SUBSET TT2 Uu)))
(dc-grind!)
(dc-focus! MAXBODY)
(quietly (lambda () (inst+ MAXSIG Uu)))
(dc-detach-impl! (list 'AND (list 'IN Uu SIG) (list 'SUBSET TT2 Uu)))   ; (= TT2 u)
(quietly (lambda () (ass-all)))
(qed (quote hb-good-has-maximal))
(topic! 'hb-good-has-maximal 'analysis)

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'NPE 'kind 'predicate 'arity 5
           'english "$5 is a norm-preserving extension of $3 from $2 to $4, in $1")
(notation! 'GOOD-SUB 'kind 'predicate 'arity 4
           'english "$3 has a norm-preserving extension from $2 to $4, in $1")
