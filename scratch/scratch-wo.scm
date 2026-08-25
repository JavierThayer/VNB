;;; scratch-wo.scm -- Well-ordering principle, proof attempt.
;;;
;;; Strategy: define wo-picks(X, alpha) cumulatively by ordinal recursion;
;;; argue via Burali-Forti that the recursion must "fill" X at some ordinal
;;; alpha_0; extract a bijection ORD-SEGMENT(alpha_0) -> X.

(load "load.scm")

;;; -----------------------------------------------------------------------
;;; Step 1: define the cumulative pick function.
;;;
;;;   wo-picks(X, 0)         = EMPTY-SET
;;;   wo-picks(X, succ alpha)
;;;       = IF X subset wo-picks(X, alpha)
;;;            then wo-picks(X, alpha)
;;;            else wo-picks(X, alpha) UNION { CHOICE(X \ wo-picks(X, alpha)) }
;;;   wo-picks(X, lam)        = UNION_{beta ORD-LT lam} wo-picks(X, beta)
;;;
;;; The IF guard is essential: it keeps wo-picks(X, alpha) subset X for all
;;; alpha, which the step-2 induction below needs.  Without the guard, once
;;; X is exhausted, CHOICE(EMPTY-SET) returns junk and the chain escapes X.

(def-by-ord-recursion 'wo-picks '(X)
  ;; base
  'EMPTY-SET
  ;; successor: vars (alpha, val); val stands in for (wo-picks X alpha)
  '(alpha val)
  '(IF (FORALL z (IMPLIES (IN z X) (IN z val)))
       val
       (UNION val (PAIR (CHOICE (COMPLEMENT-IN X val))
                        (CHOICE (COMPLEMENT-IN X val)))))
  ;; limit: var lam
  '(lam)
  '(BIG-UNION beta (ORD-SEGMENT lam) (wo-picks X beta)))

(display "--- wo-picks installed: wo-picks-zero, wo-picks-succ, wo-picks-limit ---\n")

;;; -----------------------------------------------------------------------
;;; Step 2: wo-picks(X, alpha) subset X  for alpha in ORD and X in SET.
;;;
;;; Alpha outermost so (tfi3) applies directly without prior FORALL-peeling.
;;; ((di) is greedy: peels every leading bounded FORALL at once.)

(sp (make-wff
     '(FORALL alpha (IMPLIES (IN alpha ORD)
        (FORALL X (IMPLIES (IN X SET)
            (FORALL z (IMPLIES (IN z (wo-picks X alpha)) (IN z X)))))))))

(tfi3)                          ; three subgoals: base / succ / limit

;;; --- BASE: P[alpha := 0]
;;; Goal: (FORALL X (IMPLIES (IN X SET) (FORALL z (IMPLIES (IN z (wo-picks X 0)) (IN z X)))))
(mac 'wo-picks-zero)            ; (wo-picks X 0) -> EMPTY-SET in the goal
(let* ((n  *fresh-counter*)
       (Xv (eigen-name 'X n))
       (zv (eigen-name 'z (+ n 1))))
  (di)                          ; peels FORALL X, IN X SET, FORALL z, IN z EMPTY-SET
  (ta 'empty-set-has-no-members)
  (inst '(FORALL x (NOT (IN x EMPTY-SET))) zv)
  (ai `(NOT (IN ,zv EMPTY-SET))))   ; not-elim closes via the contradiction
(display "--- step 2 base case closed ---\n")

;;; -----------------------------------------------------------------------
;;; Classical-logic helpers.  Inline the standard pbc-based proof of
;;; (OR P (NOT P)) for a specific P, then split.  Modelled on the inline
;;; pattern at proven-theorems.scm:1589-1609 (and the followups at 1836+).
;;;
;;;   (em P)     :: asserts (OR P (NOT P)) into the current assumptions.
;;;   (cases P)  :: (em P) then (ai) to split; returns the not-P-branch
;;;                 node (use (refocus! _) when ready to start that branch).

(define (em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (last-node)))
    ;; prove (OR P (NOT P))
    (pbc)                                ; assume NOT(OR P (NOT P)); goal FALSITY
    (cut `(NOT ,P))
    (let ((use-notp (last-node)))
      ;; prove (NOT P)
      (di)                               ; assume P; goal FALSITY
      (cut `(OR ,P (NOT ,P)))
      (let ((use-or2 (last-node)))
        (oi-l) (ass)
        (refocus! use-or2))
      (ai `(NOT (OR ,P (NOT ,P))))       ; closes inner FALSITY
      (refocus! use-notp))
    ;; (NOT P) now in assumptions; build the OR from it to close outer FALSITY
    (cut `(OR ,P (NOT ,P)))
    (let ((use-or3 (last-node)))
      (oi-r) (ass)
      (refocus! use-or3))
    (ai `(NOT (OR ,P (NOT ,P))))         ; closes outer FALSITY
    (refocus! use-or)))

(define (cases P)
  (em P)
  (ai `(OR ,P (NOT ,P)))
  (last-node))    ; the (NOT P) branch — caller refocuses to it when ready

;;; De Morgan helpers: turn (NOT (FORALL x P)) into (FORSOME x (NOT P))
;;; and (NOT (IMPLIES P Q)) into (AND P (NOT Q)).  No FORALL-over-wffs in
;;; VNB, so these are Scheme procedures that run an inline pbc-shaped proof
;;; for each specific instance.
;;;
;;; (not-forall) handles the bounded-FORALL form (FORALL x (IMPLIES (IN x A) Q))
;;; specially because (di) auto-peels the bound — without the special case
;;; the inner derivation would see goal Q[x:=xv] with the bound already in
;;; asms, and need to assemble the NOT-IMPLIES form by hand.

(define (not-forall forall-form)
  (let* ((x (cadr forall-form))
         (P (caddr forall-form))
         (forsome-form `(FORSOME ,x (NOT ,P)))
         (bounded? (and (pair? P) (eq? (car P) 'IMPLIES)
                        (pair? (cadr P)) (eq? (car (cadr P)) 'IN)
                        (eq? (cadr (cadr P)) x))))
    (cut forsome-form)
    (let ((useFs (last-node)))
      (pbc)                                ; assume (NOT FORSOME); goal FALSITY
      (cut forall-form)                    ; prove (FORALL x P)
      (let ((useFA (last-node)))
        (let* ((nA *fresh-counter*)
               (xv (eigen-name x nA)))
          (di)                             ; intros x; if bounded, also asm (IN xv A)
          (cond
            (bounded?
             (let* ((A   (caddr (cadr P)))
                    (Q   (caddr P))
                    (A-i (subst-free x xv A))
                    (Q-i (subst-free x xv Q))
                    (P-i `(IMPLIES (IN ,xv ,A-i) ,Q-i)))
               (pbc)                       ; assume (NOT Q-i); goal FALSITY
               (cut `(NOT ,P-i))
               (let ((useNP (last-node)))
                 (di)                      ; assume P-i; goal FALSITY
                 (cut Q-i)
                 (let ((useQ (last-node)))
                   (bc P-i)                ; goal -> (IN xv A-i)
                   (ass)
                   (refocus! useQ))
                 (ai `(NOT ,Q-i))          ; close FALSITY via contradiction
                 (refocus! useNP))
               (cut forsome-form)
               (let ((useFs2 (last-node)))
                 (ew xv)                   ; goal -> (NOT P)[x:=xv] = (NOT P-i)
                 (ass)
                 (refocus! useFs2))
               (ai `(NOT ,forsome-form)))) ; close inner FALSITY
            (else
             (let ((P-i (subst-free x xv P)))
               (pbc)
               (cut forsome-form)
               (let ((useFs2 (last-node)))
                 (ew xv) (ass)
                 (refocus! useFs2))
               (ai `(NOT ,forsome-form))))))
        (refocus! useFA))
      (ai `(NOT ,forall-form))             ; close outer FALSITY
      (refocus! useFs))))

(define (not-implies impl-form)
  (let* ((P (cadr impl-form))
         (Q (caddr impl-form))
         (and-form `(AND ,P (NOT ,Q))))
    (cut and-form)
    (let ((useAnd (last-node)))
      (di)                                 ; AND-intro: subgoal-P then subgoal-NOT-Q
      (let ((useNQ (last-node)))
        ;; subgoal: prove P
        (let ((caseNotP (cases P)))
          (ass)                            ; P branch: P in asms
          (refocus! caseNotP)
          ;; (NOT P) branch: derive vacuous (IMPLIES P Q), contradicts (NOT IMPLIES P Q)
          (cut impl-form)
          (let ((useImpl1 (last-node)))
            (di)                           ; assume P; goal Q
            (ai `(NOT ,P))                 ; closes (P + NOT P contradiction)
            (refocus! useImpl1))
          (ai `(NOT ,impl-form)))          ; closes goal P via NOT-elim
        (refocus! useNQ))
      ;; subgoal: prove (NOT Q)
      (di)                                 ; assume Q; goal FALSITY
      (cut impl-form)
      (let ((useImpl2 (last-node)))
        (di) (ass)                         ; prove (IMPLIES P Q): assume P; Q in asms; ass
        (refocus! useImpl2))
      (ai `(NOT ,impl-form))               ; closes FALSITY
      (refocus! useAnd))))

;;; -----------------------------------------------------------------------
;;; Step 2 (continued): successor case.
;;;
;;; Focus is on the tfi3 successor subgoal:
;;;   (FORALL alpha (IMPLIES (AND (IN alpha ORD) IH)
;;;                          P[alpha := succ_ORD alpha]))
;;; where IH = P(alpha) = (FORALL X (IMPLIES (IN X SET)
;;;                          (FORALL z (IMPLIES (IN z (wo-picks X alpha)) (IN z X))))).

(let* ((n0     *fresh-counter*)
       (alphav (eigen-name 'alpha n0))
       (IH     `(FORALL X (IMPLIES (IN X SET)
                   (FORALL z (IMPLIES (IN z (wo-picks X ,alphav)) (IN z X)))))))
  (di)                                  ; peels FORALL alpha
  (di)                                  ; peels IMPLIES; asm: (AND (IN alpha ORD) IH)
  (ai `(AND (IN ,alphav ORD) ,IH))      ; splits AND -> two assumptions

  ;; Now goal:
  ;;   (FORALL X (IMPLIES (IN X SET)
  ;;       (FORALL z (IMPLIES (IN z (wo-picks X (succ_ORD alpha))) (IN z X)))))
  (mac 'wo-picks-succ)                  ; rewrites (wo-picks X (succ_ORD alpha)) -> IF

  (let* ((n1 *fresh-counter*)
         (Xv (eigen-name 'X n1))
         (zv (eigen-name 'z (+ n1 1))))
    (di)                                ; peels X, IN X SET, z, IN z (IF...)
    ;; goal: (IN zv Xv)

    (let* ((WPa     `(wo-picks ,Xv ,alphav))
           (CMP     `(COMPLEMENT-IN ,Xv ,WPa))
           (CH      `(CHOICE ,CMP))
           (PAIR-CH `(PAIR ,CH ,CH))
           (TRUE-BR  WPa)
           (FALSE-BR `(UNION ,WPa ,PAIR-CH))
           (GUARD   `(FORALL z (IMPLIES (IN z ,Xv) (IN z ,WPa))))
           (IF-TERM `(IF ,GUARD ,TRUE-BR ,FALSE-BR)))

      (let ((case-notG (cases GUARD)))

        ;; ===== Branch A: GUARD in assumptions, IF reduces to TRUE-BR =====
        (if-true IF-TERM)
        (let ((useEqA (last-node)))
          (ass)                         ; subgoal 1: prove GUARD (in asms)
          (refocus! useEqA))
        ;; Subgoal 2 of if-true: (= IF-TERM TRUE-BR) in asms, goal (IN zv Xv)

        ;; Derive (IN zv TRUE-BR) = (IN zv (wo-picks Xv alphav)) in asms.
        (cut `(IN ,zv ,TRUE-BR))
        (let ((useTB (last-node)))
          (subst `(= ,TRUE-BR ,IF-TERM)) ; rewrite TRUE-BR -> IF in goal
          (ass)                          ; (IN zv IF-TERM) is in asms
          (refocus! useTB))

        ;; Apply IH to get (IN zv Xv).  IH(Xv): IMPLIES (IN Xv SET) (FORALL z ...).
        (inst IH Xv)
        (cut `(FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv))))
        (let ((useFz (last-node)))
          (bc `(IMPLIES (IN ,Xv SET) (FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv)))))
          (ass)
          (refocus! useFz))
        (inst `(FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv))) zv)
        (bc `(IMPLIES (IN ,zv ,WPa) (IN ,zv ,Xv)))
        (ass)                            ; closes goal (IN zv Xv)

        (refocus! case-notG)
        ;; ===== Branch B: (NOT GUARD) in asms, IF reduces to FALSE-BR =====
        (if-false IF-TERM)
        (let ((useEqB (last-node)))
          (ass)                       ; subgoal 1: prove (NOT GUARD) -- in asms
          (refocus! useEqB))
        ;; Subgoal 2: (= IF-TERM FALSE-BR) in asms; goal (IN zv Xv)

        ;; Move (IN zv FALSE-BR) into asms.
        (cut `(IN ,zv ,FALSE-BR))
        (let ((useFB (last-node)))
          (subst `(= ,FALSE-BR ,IF-TERM))
          (ass)
          (refocus! useFB))

        ;; union-elim splits (IN zv (UNION WPa PAIR-CH)) into two cases.
        ;; Capture B.2 node before B.1 tactics auto-advance focus.
        (ue `(IN ,zv ,FALSE-BR))
        (let ((useB2 (last-node)))

          ;; ----- B.1: (IN zv WPa) in asms ----- (same shape as Branch A's tail)
          (inst IH Xv)
          (cut `(FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv))))
          (let ((useFz1 (last-node)))
            (bc `(IMPLIES (IN ,Xv SET) (FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv)))))
            (ass)
            (refocus! useFz1))
          (inst `(FORALL z (IMPLIES (IN z ,WPa) (IN z ,Xv))) zv)
          (bc `(IMPLIES (IN ,zv ,WPa) (IN ,zv ,Xv)))
          (ass)

          ;; ----- B.2: (IN zv PAIR-CH) in asms -----
          (refocus! useB2)
        ;; Strategy: (1) derive (IN CH (COMPLEMENT-IN Xv WPa)) via NOT-GUARD + choice-axiom
        ;;           (2) extract (IN CH Xv) via complement-in-membership macete
        ;;           (3) derive (= zv CH) via pairing-membership-rev
        ;;           (4) subst zv -> CH in goal; close

        ;; Step B.2.1: get FORSOME from NOT GUARD via inline not-forall pattern.
        (not-forall GUARD)
        ;; (FORSOME z (NOT (IMPLIES (IN z Xv) (IN z WPa)))) in asms

        (let* ((nW *fresh-counter*)
               (wv (eigen-name 'z nW)))    ; binder name is z; eigen will be z_nW
          (ai `(FORSOME z (NOT (IMPLIES (IN z ,Xv) (IN z ,WPa)))))
          ;; (NOT (IMPLIES (IN wv Xv) (IN wv WPa))) in asms

          (not-implies `(IMPLIES (IN ,wv ,Xv) (IN ,wv ,WPa)))
          ;; (AND (IN wv Xv) (NOT (IN wv WPa))) in asms

          ;; Derive (IN wv (COMPLEMENT-IN Xv WPa)) via complement-in-membership.
          (cut `(IN ,wv (COMPLEMENT-IN ,Xv ,WPa)))
          (let ((useInComp (last-node)))
            (mac 'complement-in-membership)   ; goal -> (AND (IN wv Xv) (NOT (IN wv WPa)))
            (ass)
            (refocus! useInComp))
          ;; (IN wv (COMPLEMENT-IN Xv WPa)) in asms

          ;; Derive (FORSOME y (IN y (COMPLEMENT-IN Xv WPa))).
          (cut `(FORSOME y (IN y (COMPLEMENT-IN ,Xv ,WPa))))
          (let ((useFs (last-node)))
            (ew wv)
            (ass)
            (refocus! useFs))

          ;; Apply choice-axiom: get (IN CH (COMPLEMENT-IN Xv WPa)).
          (ta 'choice-axiom)
          (inst '(FORALL A (IMPLIES (FORSOME x (IN x A)) (IN (CHOICE A) A)))
                `(COMPLEMENT-IN ,Xv ,WPa))
          (cut `(IN ,CH (COMPLEMENT-IN ,Xv ,WPa)))
          (let ((useCHinComp (last-node)))
            (bc `(IMPLIES (FORSOME x (IN x (COMPLEMENT-IN ,Xv ,WPa)))
                          (IN (CHOICE (COMPLEMENT-IN ,Xv ,WPa)) (COMPLEMENT-IN ,Xv ,WPa))))
            (ass)
            (refocus! useCHinComp))

          ;; Extract (IN CH Xv) using the -rev macete.
          (cut `(AND (IN ,CH ,Xv) (NOT (IN ,CH ,WPa))))
          (let ((useAndCH (last-node)))
            (mac 'complement-in-membership-rev)  ; rewrites (AND ...) -> (IN _ (COMPLEMENT-IN _ _))
            (ass)
            (refocus! useAndCH))
          (ai `(AND (IN ,CH ,Xv) (NOT (IN ,CH ,WPa))))
          ;; (IN CH Xv) in asms, (NOT (IN CH WPa)) in asms

          ;; Derive (IN CH SET) for pairing-membership precondition.
          (ta 'membership-implies-sethood)
          (inst '(FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET)))) CH)
          (inst `(FORALL b (IMPLIES (IN ,CH b) (IN ,CH SET))) `(COMPLEMENT-IN ,Xv ,WPa))
          (cut `(IN ,CH SET))
          (let ((useCHinSET (last-node)))
            (bc `(IMPLIES (IN ,CH (COMPLEMENT-IN ,Xv ,WPa)) (IN ,CH SET)))
            (ass)
            (refocus! useCHinSET))

          ;; Pairing-membership at a := CH, b := CH, conditioned on (IN CH SET).
          (ta 'pairing-membership)
          (inst '(FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
                                              (FORALL x (IFF (IN x (PAIR a b))
                                                              (OR (= x a) (= x b)))))))
                CH)
          (inst `(FORALL b (IMPLIES (AND (IN ,CH SET) (IN b SET))
                                    (FORALL x (IFF (IN x (PAIR ,CH b))
                                                    (OR (= x ,CH) (= x b))))))
                CH)
          (cut `(FORALL x (IFF (IN x (PAIR ,CH ,CH))
                                (OR (= x ,CH) (= x ,CH)))))
          (let ((usePM (last-node)))
            (bc `(IMPLIES (AND (IN ,CH SET) (IN ,CH SET))
                          (FORALL x (IFF (IN x (PAIR ,CH ,CH))
                                          (OR (= x ,CH) (= x ,CH))))))
            (di)
            (let ((useAndS (last-node)))
              (ass) (refocus! useAndS) (ass))
            (refocus! usePM))
          (inst `(FORALL x (IFF (IN x (PAIR ,CH ,CH)) (OR (= x ,CH) (= x ,CH))))
                zv)
          ;; (IFF (IN zv (PAIR CH CH)) (OR (= zv CH) (= zv CH))) in asms.
          ;; Use the iff to derive the OR via cut + rev approach.
          (cut `(OR (= ,zv ,CH) (= ,zv ,CH)))
          (let ((useOR (last-node)))
            ;; Goal: (OR (= zv CH) (= zv CH)).  Try rewriting via the macete.
            ;; The OR is exactly the RHS of the pairing iff after specialization,
            ;; with LHS (IN zv (PAIR CH CH)) which IS in asms (the union-elim branch).
            ;; pairing-membership-rev rewrites RHS -> LHS in goal under conditions.
            (mac 'pairing-membership-rev)
            (ass)
            (refocus! useOR))

          ;; Split the (trivial) OR; both disjuncts give (= zv CH).
          (let ((useOrBr (cases `(= ,zv ,CH))))
            ;; case: (= zv CH) in asms
            (subst `(= ,zv ,CH))   ; rewrite zv -> CH in goal (IN zv Xv) -> (IN CH Xv)
            (ass)
            (refocus! useOrBr))
          ;; case: (NOT (= zv CH)) in asms.  Derive FALSITY from OR + both disjuncts equal.
          (ai `(OR (= ,zv ,CH) (= ,zv ,CH)))
          (let ((u-or-l (last-node)))
            (ai `(NOT (= ,zv ,CH)))   ; left disjunct case: (= zv CH) AND (NOT (= zv CH))
            (refocus! u-or-l)
            (ai `(NOT (= ,zv ,CH))))))
      ))))
(display "--- step 2 succ case closed ---\n")

;;; -----------------------------------------------------------------------
;;; Step 2 (continued): limit case.
;;;
;;; Focus is on the tfi3 limit subgoal:
;;;   (FORALL alpha (IMPLIES (AND (LIMIT-ORD alpha) IH-limit) P(alpha)))
;;; where IH-limit = (FORALL beta (IMPLIES (ORD-LT beta alpha) P(beta)))
;;; and P(alpha) = (FORALL X (IMPLIES (IN X SET)
;;;                   (FORALL z (IMPLIES (IN z (wo-picks X alpha)) (IN z X))))).
;;;
;;; Strategy: peel alpha, split the AND, derive (IN alpha ORD) from (LIMIT-ORD
;;; alpha) via the auto-installed limit-ord-iff-rev macete, then mac
;;; wo-picks-limit to rewrite into a BIG-UNION.  big-union-mem-elim yields
;;; a witness beta with z in wo-picks(X, beta); ord-segment-membership gives
;;; (ORD-LT beta alpha); IH-limit then yields (IN z X).

(let* ((nL0    *fresh-counter*)
       (alphav (eigen-name 'alpha nL0)))
  (di)                                  ; intro alpha
  (di)                                  ; assume (AND (LIMIT-ORD alpha) IH-limit)

  (let* ((IH-limit `(FORALL beta (IMPLIES (ORD-LT beta ,alphav)
                       (FORALL X (IMPLIES (IN X SET)
                          (FORALL z (IMPLIES (IN z (wo-picks X beta)) (IN z X))))))))
         (LIM-AND  `(AND (IN ,alphav ORD)
                         (AND (NOT (= ,alphav 0))
                              (NOT (FORSOME alpha (AND (IN alpha ORD)
                                                       (= ,alphav (succ_ORD alpha)))))))))
    (ai `(AND (LIMIT-ORD ,alphav) ,IH-limit))
    ;; asms: (LIMIT-ORD alphav), IH-limit; goal: P(alphav)

    ;; Derive (IN alphav ORD) via limit-ord-iff-rev (auto-installed).
    (cut LIM-AND)
    (let ((useLim (last-node)))
      (mac 'limit-ord-iff-rev)         ; goal (AND ...) -> (LIMIT-ORD alphav)
      (ass)
      (refocus! useLim))
    (ai LIM-AND)                       ; splits AND; (IN alphav ORD) into asms

    ;; Now mac wo-picks-limit fires (condition (LIMIT-ORD alphav) holds).
    (mac 'wo-picks-limit)

    (let* ((nL1 *fresh-counter*)
           (Xv  (eigen-name 'X nL1))
           (zv  (eigen-name 'z (+ nL1 1))))
      (di)                              ; peels X, IN X SET, z, IN z (BIG-UNION ...)

      ;; bu-me extracts witness beta_w with (IN beta_w (ORD-SEGMENT alphav))
      ;; and (IN zv (wo-picks Xv beta_w)) in asms.  Snapshot counter BEFORE
      ;; the call (fresh-var consumes the current value and advances).
      (let* ((nL2   *fresh-counter*)
             (betaw (eigen-name 'beta nL2)))
        (bu-me `(IN ,zv (BIG-UNION beta (ORD-SEGMENT ,alphav) (wo-picks ,Xv beta))))

        ;; Derive (ORD-LT betaw alphav) via ord-segment-membership-rev macete.
        (cut `(ORD-LT ,betaw ,alphav))
        (let ((useLT (last-node)))
          (mac 'ord-segment-membership-rev)  ; goal (ORD-LT x alpha) -> (IN x (ORD-SEGMENT alpha))
          (ass)
          (refocus! useLT))

        ;; Apply IH-limit at betaw.
        (inst IH-limit betaw)
        (cut `(FORALL X (IMPLIES (IN X SET)
                  (FORALL z (IMPLIES (IN z (wo-picks X ,betaw)) (IN z X))))))
        (let ((useP-b (last-node)))
          (bc `(IMPLIES (ORD-LT ,betaw ,alphav)
                        (FORALL X (IMPLIES (IN X SET)
                            (FORALL z (IMPLIES (IN z (wo-picks X ,betaw)) (IN z X)))))))
          (ass)
          (refocus! useP-b))

        ;; Now P(betaw) in asms.  Apply at Xv and zv.
        (inst `(FORALL X (IMPLIES (IN X SET)
                  (FORALL z (IMPLIES (IN z (wo-picks X ,betaw)) (IN z X)))))
              Xv)
        (cut `(FORALL z (IMPLIES (IN z (wo-picks ,Xv ,betaw)) (IN z ,Xv))))
        (let ((useFz (last-node)))
          (bc `(IMPLIES (IN ,Xv SET)
                        (FORALL z (IMPLIES (IN z (wo-picks ,Xv ,betaw)) (IN z ,Xv)))))
          (ass)
          (refocus! useFz))
        (inst `(FORALL z (IMPLIES (IN z (wo-picks ,Xv ,betaw)) (IN z ,Xv))) zv)
        (bc `(IMPLIES (IN ,zv (wo-picks ,Xv ,betaw)) (IN ,zv ,Xv)))
        (ass)))))
(display "--- step 2 limit case closed ---\n")

;;; -----------------------------------------------------------------------
;;; Install as theorem.
(qed 'wo-picks-subset-X)
(display "--- wo-picks-subset-X installed ---\n")

;;; =======================================================================
;;; HELPER LEMMA: ord-lt-succ-le
;;;
;;;   forall alpha beta in ORD,
;;;       (ORD-LT alpha (succ_ORD beta))  =>  (ORD-LE alpha beta).
;;;
;;; Standard ordinal fact -- alpha strictly below succ beta means alpha is at
;;; most beta.  Not present in the codebase; proven here for use in the
;;; monotonicity proof's successor case (and step 3's injectivity argument).
;;; =======================================================================

(sp (make-wff
     '(FORALL alpha (FORALL beta
         (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD) (ORD-LT alpha (succ_ORD beta))))
                  (ORD-LE alpha beta))))))

(let* ((nLS0   *fresh-counter*)
       (alphav (eigen-name 'alpha nLS0))
       (betav  (eigen-name 'beta  (+ nLS0 1))))
  (di)                                  ; peels FORALL alpha FORALL beta
  (di)                                  ; peels IMPLIES
  (ai `(AND (IN ,alphav ORD) (AND (IN ,betav ORD) (ORD-LT ,alphav (succ_ORD ,betav)))))
  (ai `(AND (IN ,betav  ORD) (ORD-LT ,alphav (succ_ORD ,betav))))
  ;; asms: (IN alpha ORD), (IN beta ORD), (ORD-LT alpha (succ beta));  goal: (ORD-LE alpha beta)

  ;; Derive (ORD-LE alpha (succ beta)) and (NOT (= alpha (succ beta))) up front.
  (cut `(AND (ORD-LE ,alphav (succ_ORD ,betav)) (NOT (= ,alphav (succ_ORD ,betav)))))
  (let ((u-and-lt (last-node)))
    (mac 'ord-lt-iff-rev)               ; (AND ...) <- (ORD-LT ...) ; rewrites goal back
    (ass)
    (refocus! u-and-lt))
  (ai `(AND (ORD-LE ,alphav (succ_ORD ,betav)) (NOT (= ,alphav (succ_ORD ,betav)))))

  ;; (pbc): assume (NOT (ORD-LE alpha beta)); goal FALSITY.
  (pbc)

  ;; From ord-le-total derive the OR.
  (cut `(OR (ORD-LE ,alphav ,betav) (ORD-LE ,betav ,alphav)))
  (let ((useOR (last-node)))
    (ta 'ord-le-total)
    (inst '(FORALL alpha (FORALL beta (IMPLIES (AND (IN alpha ORD) (IN beta ORD))
                                                (OR (ORD-LE alpha beta) (ORD-LE beta alpha)))))
          alphav)
    (inst `(FORALL beta (IMPLIES (AND (IN ,alphav ORD) (IN beta ORD))
                                  (OR (ORD-LE ,alphav beta) (ORD-LE beta ,alphav))))
          betav)
    (bc `(IMPLIES (AND (IN ,alphav ORD) (IN ,betav ORD))
                  (OR (ORD-LE ,alphav ,betav) (ORD-LE ,betav ,alphav))))
    (di)
    (let ((u-and (last-node)))
      (ass) (refocus! u-and) (ass))
    (refocus! useOR))

  (ai `(OR (ORD-LE ,alphav ,betav) (ORD-LE ,betav ,alphav)))
  (let ((u-or2 (last-node)))
    ;; Case 1: (ORD-LE alpha beta) -- contradicts (NOT (ORD-LE alpha beta))
    (ai `(NOT (ORD-LE ,alphav ,betav)))
    (refocus! u-or2)

    ;; Case 2: (ORD-LE beta alpha).  Sub-case on (= beta alpha).
    (let ((u-case-eq (cases `(= ,betav ,alphav))))
      ;; Sub-case (= beta alpha): derive (ORD-LE alpha beta) via refl + subst
      (cut `(ORD-LE ,alphav ,betav))
      (let ((u-le (last-node)))
        (subst `(= ,betav ,alphav))
        (ta 'ord-le-refl)
        (inst '(FORALL alpha (IMPLIES (IN alpha ORD) (ORD-LE alpha alpha))) alphav)
        (bc `(IMPLIES (IN ,alphav ORD) (ORD-LE ,alphav ,alphav)))
        (ass)
        (refocus! u-le))
      (ai `(NOT (ORD-LE ,alphav ,betav)))
      (refocus! u-case-eq)

      ;; Sub-case (NOT (= beta alpha)): derive (ORD-LT beta alpha) via ord-lt-iff (forward).
      (cut `(ORD-LT ,betav ,alphav))
      (let ((u-lt (last-node)))
        (mac 'ord-lt-iff)               ; (ORD-LT beta alpha) -> (AND (ORD-LE beta alpha) (NOT (= beta alpha)))
        (di)
        (let ((u-and2 (last-node)))
          (ass) (refocus! u-and2) (ass))
        (refocus! u-lt))

      ;; By ord-succ-immediate: (ORD-LE (succ beta) alpha).
      (cut `(ORD-LE (succ_ORD ,betav) ,alphav))
      (let ((u-le2 (last-node)))
        (ta 'ord-succ-immediate)
        (inst '(FORALL alpha (FORALL beta (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD) (ORD-LT alpha beta)))
                                                    (ORD-LE (succ_ORD alpha) beta))))
              betav)
        (inst `(FORALL beta (IMPLIES (AND (IN ,betav ORD) (AND (IN beta ORD) (ORD-LT ,betav beta)))
                                      (ORD-LE (succ_ORD ,betav) beta)))
              alphav)
        (bc `(IMPLIES (AND (IN ,betav ORD) (AND (IN ,alphav ORD) (ORD-LT ,betav ,alphav)))
                      (ORD-LE (succ_ORD ,betav) ,alphav)))
        (di)
        (let ((u-3 (last-node)))
          (ass)                         ; (IN beta ORD)
          (refocus! u-3)
          (di)
          (let ((u-3b (last-node)))
            (ass)                       ; (IN alpha ORD)
            (refocus! u-3b)
            (ass)))                     ; (ORD-LT beta alpha)
        (refocus! u-le2))

      ;; (ORD-LE (succ beta) alpha) and (ORD-LE alpha (succ beta)) in asms -> antisymm.
      (cut `(= (succ_ORD ,betav) ,alphav))
      (let ((u-eq (last-node)))
        (ta 'ord-le-antisymm)
        (inst '(FORALL alpha (FORALL beta (IMPLIES (AND (ORD-LE alpha beta) (ORD-LE beta alpha))
                                                    (= alpha beta))))
              `(succ_ORD ,betav))
        (inst `(FORALL beta (IMPLIES (AND (ORD-LE (succ_ORD ,betav) beta) (ORD-LE beta (succ_ORD ,betav)))
                                      (= (succ_ORD ,betav) beta)))
              alphav)
        (bc `(IMPLIES (AND (ORD-LE (succ_ORD ,betav) ,alphav) (ORD-LE ,alphav (succ_ORD ,betav)))
                      (= (succ_ORD ,betav) ,alphav)))
        (di)
        (let ((u-and4 (last-node)))
          (ass) (refocus! u-and4) (ass))
        (refocus! u-eq))

      ;; Flip equality via subst+rfl to match (NOT (= alpha (succ beta))).
      (cut `(= ,alphav (succ_ORD ,betav)))
      (let ((u-eq2 (last-node)))
        (subst `(= (succ_ORD ,betav) ,alphav))
        (rfl)
        (refocus! u-eq2))

      (ai `(NOT (= ,alphav (succ_ORD ,betav)))))))
(qed 'ord-lt-succ-le)
(display "--- ord-lt-succ-le installed ---\n")

;;; =======================================================================
;;; LEMMA: monotonicity of wo-picks.
;;;   forall X in SET, forall alpha beta in ORD,
;;;       alpha ORD-LE beta  =>
;;;         forall z, z in wo-picks(X, alpha) -> z in wo-picks(X, beta).
;;;
;;; Three-case transfinite induction on beta (outermost so tfi3 applies).
;;; Successor uses ord-lt-succ-le to reduce alpha <= succ beta' to alpha <= beta'.
;;; Limit uses big-union-mem-intro to inject wo-picks(X, alpha) into the union.
;;; =======================================================================

(sp (make-wff
     '(FORALL beta (IMPLIES (IN beta ORD)
        (FORALL X (IMPLIES (IN X SET)
            (FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha beta))
                (FORALL z (IMPLIES (IN z (wo-picks X alpha))
                                   (IN z (wo-picks X beta))))))))))))

(tfi3)

;;; ---- BASE: beta = 0 ----
(let* ((nMB *fresh-counter*)
       (Xv0     (eigen-name 'X     nMB))
       (alpha0  (eigen-name 'alpha (+ nMB 1))))
  (di)                                  ; peels FORALL X (with IN X SET), FORALL alpha (no bound, AND in body)
  (di)                                  ; peels IMPLIES
  (ai `(AND (IN ,alpha0 ORD) (ORD-LE ,alpha0 0)))
  (let* ((nMB2 *fresh-counter*)
         (zv0 (eigen-name 'z nMB2)))
    (di)                                ; peels FORALL z (IN z (wo-picks X alpha) bound)
    ;; goal: (IN zv0 (wo-picks Xv0 0))

    ;; Derive (= alpha0 0) via antisymm of ORD-LE with (ORD-LE 0 alpha0).
    (cut `(= ,alpha0 0))
    (let ((u-eq (last-node)))
      (ta 'ord-le-antisymm)
      (inst '(FORALL alpha (FORALL beta (IMPLIES (AND (ORD-LE alpha beta) (ORD-LE beta alpha))
                                                  (= alpha beta))))
            alpha0)
      (inst `(FORALL beta (IMPLIES (AND (ORD-LE ,alpha0 beta) (ORD-LE beta ,alpha0))
                                    (= ,alpha0 beta))) 0)
      (bc `(IMPLIES (AND (ORD-LE ,alpha0 0) (ORD-LE 0 ,alpha0)) (= ,alpha0 0)))
      (di)
      (let ((u-le (last-node)))
        (ass)
        (refocus! u-le)
        (ta 'ord-zero-least)
        (inst '(FORALL alpha (IMPLIES (IN alpha ORD) (ORD-LE 0 alpha))) alpha0)
        (bc `(IMPLIES (IN ,alpha0 ORD) (ORD-LE 0 ,alpha0)))
        (ass))
      (refocus! u-eq))
    (subst `(= 0 ,alpha0))
    (ass)))
(display "--- monotone base case closed ---\n")

;;; ---- SUCC: beta = succ beta' ----
;;; Subgoal: (FORALL beta' (IMPLIES (AND (IN beta' ORD) P(beta')) P(succ beta'))).
;;; After di/di/ai, asms: (IN beta' ORD), P(beta');  goal: P(succ beta').

(let* ((nMS0 *fresh-counter*)
       (betap (eigen-name 'beta nMS0)))
  (di)                                  ; peels FORALL beta'
  (di)                                  ; peels IMPLIES
  (let ((IH-P `(FORALL X (IMPLIES (IN X SET)
                  (FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha ,betap))
                      (FORALL z (IMPLIES (IN z (wo-picks X alpha))
                                         (IN z (wo-picks X ,betap))))))))))
    (ai `(AND (IN ,betap ORD) ,IH-P))

    (let* ((nMS1 *fresh-counter*)
           (Xvs    (eigen-name 'X     nMS1))
           (alphav (eigen-name 'alpha (+ nMS1 1))))
      (di)                              ; peels FORALL X (IN X SET), FORALL alpha
      (di)                              ; peels IMPLIES
      (ai `(AND (IN ,alphav ORD) (ORD-LE ,alphav (succ_ORD ,betap))))
      (let* ((nMS2 *fresh-counter*)
             (zvs (eigen-name 'z nMS2)))
        (di)                            ; peels FORALL z (IN z (wo-picks X alpha) bound)
        ;; goal: (IN zvs (wo-picks Xvs (succ_ORD betap)))
        ;; asms include: (IN alphav ORD), (ORD-LE alphav (succ_ORD betap)), (IN zvs (wo-picks Xvs alphav))

        ;; Case-split on (= alphav (succ_ORD betap)).
        (let ((u-case-ne (cases `(= ,alphav (succ_ORD ,betap)))))
          ;; Case (= alphav (succ betap)): rewrite (succ betap) -> alphav in goal.
          (subst `(= (succ_ORD ,betap) ,alphav))
          (ass)
          (refocus! u-case-ne))

        ;; NOT (= alpha (succ beta')): get alpha ORD-LT succ beta', then alpha ORD-LE beta' via ord-lt-succ-le,
        ;; then IH gives z in wo-picks(X, beta'), then single-step gives wo-picks(X, succ beta').

        ;; Step S1: (ORD-LT alpha (succ beta')).
        (cut `(ORD-LT ,alphav (succ_ORD ,betap)))
        (let ((u-lt (last-node)))
          (mac 'ord-lt-iff)             ; (ORD-LT a b) -> (AND (ORD-LE a b) (NOT (= a b)))
          (di)
          (let ((u-and (last-node)))
            (ass) (refocus! u-and) (ass))
          (refocus! u-lt))

        ;; Step S2: (ORD-LE alpha beta') via ord-lt-succ-le.
        (cut `(ORD-LE ,alphav ,betap))
        (let ((u-le-ab (last-node)))
          (ta 'ord-lt-succ-le)
          (inst '(FORALL alpha (FORALL beta
                    (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD) (ORD-LT alpha (succ_ORD beta))))
                             (ORD-LE alpha beta))))
                alphav)
          (inst `(FORALL beta (IMPLIES (AND (IN ,alphav ORD) (AND (IN beta ORD) (ORD-LT ,alphav (succ_ORD beta))))
                                        (ORD-LE ,alphav beta)))
                betap)
          (bc `(IMPLIES (AND (IN ,alphav ORD) (AND (IN ,betap ORD) (ORD-LT ,alphav (succ_ORD ,betap))))
                        (ORD-LE ,alphav ,betap)))
          (di)
          (let ((u-3 (last-node)))
            (ass)
            (refocus! u-3)
            (di)
            (let ((u-3b (last-node)))
              (ass) (refocus! u-3b) (ass)))
          (refocus! u-le-ab))

        ;; Step S3: IH instantiated at Xvs, alphav, zvs gives (IN zvs (wo-picks Xvs betap)).
        (cut `(IN ,zvs (wo-picks ,Xvs ,betap)))
        (let ((u-in-beta (last-node)))
          (inst IH-P Xvs)
          (cut `(FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha ,betap))
                    (FORALL z (IMPLIES (IN z (wo-picks ,Xvs alpha))
                                       (IN z (wo-picks ,Xvs ,betap))))))
            )
          (let ((u-IH-X (last-node)))
            (bc `(IMPLIES (IN ,Xvs SET)
                          (FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha ,betap))
                              (FORALL z (IMPLIES (IN z (wo-picks ,Xvs alpha))
                                                 (IN z (wo-picks ,Xvs ,betap))))))))
            (ass)
            (refocus! u-IH-X))
          (inst `(FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha ,betap))
                    (FORALL z (IMPLIES (IN z (wo-picks ,Xvs alpha))
                                       (IN z (wo-picks ,Xvs ,betap))))))
                alphav)
          (cut `(FORALL z (IMPLIES (IN z (wo-picks ,Xvs ,alphav)) (IN z (wo-picks ,Xvs ,betap))))
            )
          (let ((u-IH-z (last-node)))
            (bc `(IMPLIES (AND (IN ,alphav ORD) (ORD-LE ,alphav ,betap))
                          (FORALL z (IMPLIES (IN z (wo-picks ,Xvs ,alphav))
                                             (IN z (wo-picks ,Xvs ,betap))))))
            (di)
            (let ((u-and2 (last-node)))
              (ass) (refocus! u-and2) (ass))
            (refocus! u-IH-z))
          (inst `(FORALL z (IMPLIES (IN z (wo-picks ,Xvs ,alphav)) (IN z (wo-picks ,Xvs ,betap)))) zvs)
          (bc `(IMPLIES (IN ,zvs (wo-picks ,Xvs ,alphav)) (IN ,zvs (wo-picks ,Xvs ,betap))))
          (ass)
          (refocus! u-in-beta))

        ;; Step S4: from (IN zvs (wo-picks Xvs betap)) derive (IN zvs (wo-picks Xvs (succ betap))).
        ;; mac wo-picks-succ on goal -> IF expression.  Case-split on guard.
        (mac 'wo-picks-succ)
        (let* ((WPB `(wo-picks ,Xvs ,betap))
               (CMPB `(COMPLEMENT-IN ,Xvs ,WPB))
               (CHB `(CHOICE ,CMPB))
               (PAIRB `(PAIR ,CHB ,CHB))
               (GUARDB `(FORALL z (IMPLIES (IN z ,Xvs) (IN z ,WPB))))
               (IFB `(IF ,GUARDB ,WPB (UNION ,WPB ,PAIRB))))
          (let ((u-case-G (cases GUARDB)))
            ;; True: IF -> WPB. Goal: (IN zvs IF). After if-true subst, goal (IN zvs WPB). ass.
            (if-true IFB)
            (let ((u-eqT (last-node)))
              (ass)                     ; prove GUARDB (in asms via cases)
              (refocus! u-eqT))
            (subst `(= ,IFB ,WPB))
            (ass)
            (refocus! u-case-G))

          ;; NOT GUARDB: IF -> UNION WPB PAIRB. Goal (IN zvs IF) ; after if-false subst, goal (IN zvs UNION).
          (if-false `(IF ,GUARDB ,WPB (UNION ,WPB ,PAIRB)))
          (let ((u-eqF (last-node)))
            (ass)
            (refocus! u-eqF))
          (subst `(= (IF ,GUARDB ,WPB (UNION ,WPB ,PAIRB)) (UNION ,WPB ,PAIRB)))
          ;; goal: (IN zvs (UNION WPB PAIRB)). Use ui (union-intro) selecting left (index 1).
          (ui 1)
          ;; goal: (IN zvs WPB), in asms.
          (ass))))))
(display "--- monotone succ case closed ---\n")

;;; ---- LIMIT: beta = lambda ----
;;; Subgoal: (FORALL beta (IMPLIES (AND (LIMIT-ORD beta) IH-limit) P(beta))).
;;; The outer binder is 'beta (same name as the original outermost FORALL var);
;;; (di) allocates a beta-eigen.  IH-L's inner binder is some 'beta_K from tfi3;
;;; we use a generic name 'b and rely on alpha-equivalence in asms-find.
(let* ((nML0 *fresh-counter*)
       (lambv (eigen-name 'beta nML0)))
  (di)                                  ; peels FORALL beta (outer)
  (di)                                  ; peels IMPLIES
  (let ((IH-L `(FORALL b (IMPLIES (ORD-LT b ,lambv)
                  (FORALL X (IMPLIES (IN X SET)
                      (FORALL alpha (IMPLIES (AND (IN alpha ORD) (ORD-LE alpha b))
                          (FORALL z (IMPLIES (IN z (wo-picks X alpha))
                                             (IN z (wo-picks X b))))))))))))
    (ai `(AND (LIMIT-ORD ,lambv) ,IH-L))

    ;; Derive (IN lambv ORD) via limit-ord-iff-rev.
    (let ((LIM-AND `(AND (IN ,lambv ORD)
                         (AND (NOT (= ,lambv 0))
                              (NOT (FORSOME alpha (AND (IN alpha ORD)
                                                       (= ,lambv (succ_ORD alpha)))))))))
      (cut LIM-AND)
      (let ((u-lim (last-node)))
        (mac 'limit-ord-iff-rev)
        (ass)
        (refocus! u-lim))
      (ai LIM-AND))

    (let* ((nML1 *fresh-counter*)
           (Xvl    (eigen-name 'X     nML1))
           (alphal (eigen-name 'alpha (+ nML1 1))))
      (di)
      (di)
      (ai `(AND (IN ,alphal ORD) (ORD-LE ,alphal ,lambv)))
      (let* ((nML2 *fresh-counter*)
             (zvl (eigen-name 'z nML2)))
        (di)
        ;; asms: (IN alphal ORD), (ORD-LE alphal lambv), (IN zvl (wo-picks Xvl alphal))
        ;; goal: (IN zvl (wo-picks Xvl lambv))

        (let ((u-case-eq (cases `(= ,alphal ,lambv))))
          ;; (= alphal lambv): rewrite lambv -> alphal in goal.
          (subst `(= ,lambv ,alphal))
          (ass)
          (refocus! u-case-eq))

        ;; NOT (= alpha lambda): derive (ORD-LT alpha lambda) and use IH-L.
        (cut `(ORD-LT ,alphal ,lambv))
        (let ((u-lt (last-node)))
          (mac 'ord-lt-iff)
          (di)
          (let ((u-and (last-node)))
            (ass) (refocus! u-and) (ass))
          (refocus! u-lt))

        ;; mac wo-picks-limit on goal -> BIG-UNION (LIMIT-ORD lambv is in asms).
        (mac 'wo-picks-limit)
        ;; goal: (IN zvl (BIG-UNION beta (ORD-SEGMENT lambv) (wo-picks Xvl beta)))
        ;; Use bu-mi with witness alphal.
        (bu-mi alphal)
        ;; Two subgoals from bu-mi:
        ;;   (IN alphal (ORD-SEGMENT lambv))   and   (IN zvl (wo-picks Xvl alphal))
        (let ((u-snd (last-node)))
          ;; First subgoal: rewrite (IN alphal (ORD-SEGMENT lambv)) to (ORD-LT alphal lambv) which is in asms.
          (mac 'ord-segment-membership)
          (ass)
          (refocus! u-snd))
        (ass)))))
(display "--- monotone limit case closed ---\n")

(qed 'wo-picks-monotone)
(display "--- wo-picks-monotone installed ---\n")

;;; =======================================================================
;;; LEMMA (set-from-injection): if j : X -> A is an injective functoid into
;;; a SET A, then X is a SET.
;;;
;;; Proof:
;;;   For each a in A, define k(a) := { s in X : j(s) = a }.
;;;   By inj, k(a) is either empty or a singleton, hence a set.
;;;   K := big-union_{a in A} k(a) is a set by the big-union axiom.
;;;   By class-extensionality, K = X (they have the same elements).
;;;   Therefore X is a set.
;;; =======================================================================

;; Outer binders use non-letter-collision names: cls (class), st (set), fn (fn).
;; MIT case-folds; if we used X / x both, the inner FORALL x would shadow X.
(sp (make-wff
     '(FORALL cls (FORALL st (FORALL fn
        (IMPLIES (AND (IN st SET)
                      (AND (FORALL x (IMPLIES (IN x cls) (IN (fn x) st)))
                           (FORALL x (FORALL y
                              (IMPLIES (AND (IN x cls) (AND (IN y cls) (= (fn x) (fn y))))
                                       (= x y))))))
                 (IN cls SET)))))))

(let* ((nL0 *fresh-counter*)
       (Cv (eigen-name 'cls nL0))       ; the class
       (Sv (eigen-name 'st  (+ nL0 1))) ; the set
       (Fv (eigen-name 'fn  (+ nL0 2))) ; the functoid
       (Fv-of (lambda (a) `(,Fv ,a)))
       (TOTAL `(FORALL x (IMPLIES (IN x ,Cv) (IN (,Fv x) ,Sv))))
       (INJ   `(FORALL x (FORALL y
                  (IMPLIES (AND (IN x ,Cv) (AND (IN y ,Cv) (= (,Fv x) (,Fv y))))
                           (= x y))))))
  (di)                                  ; peels FORALL X, FORALL A, FORALL j
  (di)                                  ; peels IMPLIES; asm is the AND
  (display ";;; DEBUG: about to (ai) the AND.  Asms:\n")
  (show)
  (display ";;; DEBUG: my AND form is:\n")
  (write `(AND (IN ,Sv SET) (AND ,TOTAL ,INJ))) (newline)
  (ai `(AND (IN ,Sv SET) (AND ,TOTAL ,INJ)))
  (ai `(AND ,TOTAL ,INJ))
  ;; asms: (IN Sv SET), TOTAL, INJ;  goal: (IN Cv SET)

  ;; Define k(a) and K as Scheme-side abbreviations.
  (let* ((k-of-a `(COMP s (AND (IN s ,Cv) (= (,Fv s) a))))
         (K `(BIG-UNION a ,Sv ,k-of-a)))

    ;;; -----------------------------------------------------------------
    ;;; Part 1: prove (IN K SET).
    (cut `(IN ,K SET))
    (let ((u-Kset (last-node)))
      (let ((nBU *fresh-counter*))
        (bu-set)
        ;; subgoal 1: (IN Sv SET) -- in asms.
        (let ((u-bu2 (last-node)))
          (ass)
          (refocus! u-bu2))

        ;; subgoal 2: (FORALL a (IMPLIES (IN a Sv) (IN k(a) SET))).
        (let* ((bu-binder (eigen-name 'a nBU))
               (nDI *fresh-counter*)
               (av (eigen-name bu-binder nDI)))
          (di)                          ; peels FORALL a, IN a Sv into asms
          ;; goal: (IN k(av) SET) where k(av) = COMP s (AND (IN s Cv) (= (Fv s) av))

          (let* ((k-av `(COMP s (AND (IN s ,Cv) (= (,Fv s) ,av))))
                 (G-a `(FORSOME s (AND (IN s ,Cv) (= (,Fv s) ,av)))))
            (let ((u-case-empty (cases G-a)))

              ;;; ----- Singleton case: G-a holds -----
              ;; Let s0 := CHOICE(k-av).  Show: k-av = PAIR(s0, s0) via class-ext.

              ;; First derive s0 in k-av via choice-axiom + G-a's witness.
              (cut `(IN (CHOICE ,k-av) ,k-av))
              (let ((u-s0-in (last-node)))
                (ta 'choice-axiom)
                (inst '(FORALL A (IMPLIES (FORSOME x (IN x A)) (IN (CHOICE A) A))) k-av)
                (bc `(IMPLIES (FORSOME x (IN x ,k-av)) (IN (CHOICE ,k-av) ,k-av)))
                ;; goal: (FORSOME x (IN x k-av)).  Witness from G-a.
                (let* ((nW *fresh-counter*)
                       (sw (eigen-name 's nW)))
                  (ai G-a)
                  (ai `(AND (IN ,sw ,Cv) (= (,Fv ,sw) ,av)))
                  (ew sw)
                  ;; goal: (IN sw k-av) = (IN sw (COMP s (AND ...)))
                  (comp-mi)
                  (let ((u-cmi (last-node)))
                    ;; subgoal 1: (IN sw SET)
                    (ta 'membership-implies-sethood)
                    (inst '(FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET)))) sw)
                    (inst `(FORALL b (IMPLIES (IN ,sw b) (IN ,sw SET))) Cv)
                    (bc `(IMPLIES (IN ,sw ,Cv) (IN ,sw SET)))
                    (ass)
                    (refocus! u-cmi))
                  ;; subgoal 2: (AND (IN sw Cv) (= (Fv sw) av)) -- in asms
                  (di)
                  (let ((u-and (last-node)))
                    (ass) (refocus! u-and) (ass)))
                (refocus! u-s0-in))

              ;; By comp-me on (IN (CHOICE k-av) k-av):
              ;;   adds (IN (CHOICE k-av) SET) and the body AND.
              (comp-me `(IN (CHOICE ,k-av) ,k-av))
              (ai `(AND (IN (CHOICE ,k-av) ,Cv) (= (,Fv (CHOICE ,k-av)) ,av)))

              ;; Now show k-av = PAIR(CHOICE, CHOICE) via class-extensionality.
              (cut `(= ,k-av (PAIR (CHOICE ,k-av) (CHOICE ,k-av))))
              (let ((u-keq (last-node)))
                (ta 'class-extensionality)
                (inst '(FORALL A (FORALL B (IMPLIES (FORALL x (IFF (IN x A) (IN x B)))
                                                     (= A B))))
                      k-av)
                (inst `(FORALL B (IMPLIES (FORALL x (IFF (IN x ,k-av) (IN x B)))
                                          (= ,k-av B)))
                      `(PAIR (CHOICE ,k-av) (CHOICE ,k-av)))
                (bc `(IMPLIES (FORALL x (IFF (IN x ,k-av) (IN x (PAIR (CHOICE ,k-av) (CHOICE ,k-av)))))
                              (= ,k-av (PAIR (CHOICE ,k-av) (CHOICE ,k-av)))))
                ;; goal: (FORALL x (IFF (IN x k-av) (IN x (PAIR (CHOICE k-av) (CHOICE k-av)))))
                (let* ((nXE *fresh-counter*)
                       (xe (eigen-name 'x nXE)))
                  (di)                  ; intro x
                  (di)                  ; IFF: split into two implies
                  ;; subgoal a: (IN xe k-av) -> (IN xe PAIR(c, c))
                  ;; iff-intro already moved (IN xe k-av) into asms.
                  (let ((u-iff-b (last-node)))
                    (comp-me `(IN ,xe ,k-av))
                    (ai `(AND (IN ,xe ,Cv) (= (,Fv ,xe) ,av)))
                    ;; Apply INJ at xe and CHOICE(k-av) to get (= xe (CHOICE k-av)).
                    (cut `(= ,xe (CHOICE ,k-av)))
                    (let ((u-eq-x-c (last-node)))
                      (inst INJ xe)
                      (inst `(FORALL y (IMPLIES (AND (IN ,xe ,Cv)
                                                      (AND (IN y ,Cv) (= (,Fv ,xe) (,Fv y))))
                                                (= ,xe y)))
                            `(CHOICE ,k-av))
                      (bc `(IMPLIES (AND (IN ,xe ,Cv)
                                          (AND (IN (CHOICE ,k-av) ,Cv) (= (,Fv ,xe) (,Fv (CHOICE ,k-av)))))
                                    (= ,xe (CHOICE ,k-av))))
                      (di)
                      (let ((u-and1 (last-node)))
                        (ass)                                   ; (IN xe Cv) in asms
                        (refocus! u-and1)
                        (di)
                        (let ((u-and2 (last-node)))
                          (ass)                                 ; (IN CHOICE Cv) in asms
                          (refocus! u-and2)
                          ;; goal: (= Fv-xe Fv-CHOICE).  (= Fv-xe av) and (= Fv-CHOICE av) in asms.
                          (subst `(= ,(Fv-of xe) ,av))                       ; Fv-xe -> av
                          (subst `(= ,(Fv-of `(CHOICE ,k-av)) ,av))         ; Fv-CHOICE -> av
                          (rfl)))
                      (refocus! u-eq-x-c))
                    ;; (= xe (CHOICE k-av)) in asms.  Goal: (IN xe PAIR(CHOICE, CHOICE)).
                    (subst `(= ,xe (CHOICE ,k-av)))    ; rewrite xe -> CHOICE in goal
                    ;; goal: (IN CHOICE PAIR(CHOICE, CHOICE))
                    ;; (IN CHOICE SET) is in asms; pairing-membership rewrites IN-PAIR to OR.
                    (mac 'pairing-membership)
                    ;; goal: (OR (= CHOICE CHOICE) (= CHOICE CHOICE))
                    (oi-l)
                    (rfl)
                    (refocus! u-iff-b))
                  ;; subgoal b: (IN xe PAIR(c, c)) in asms; goal (IN xe k-av).
                  ;; iff-intro already moved (IN xe PAIR) into asms.
                  ;; Strategy: derive (= xe CHOICE) via pairing-membership-rev,
                  ;; then comp-mi the goal and discharge.
                  (cut `(= ,xe (CHOICE ,k-av)))
                  (let ((u-eqB (last-node)))
                    ;; Derive (OR (= xe c) (= xe c)) by reverse-rewriting against
                    ;; (IN xe PAIR(c,c)).
                    (cut `(OR (= ,xe (CHOICE ,k-av)) (= ,xe (CHOICE ,k-av))))
                    (let ((u-orB (last-node)))
                      (mac 'pairing-membership-rev)             ; goal OR -> IN PAIR
                      (ass)                                      ; (IN xe PAIR) in asms
                      (refocus! u-orB))
                    ;; (OR (= xe c) (= xe c)) in asms.  Goal: (= xe c).
                    (ai `(OR (= ,xe (CHOICE ,k-av)) (= ,xe (CHOICE ,k-av))))
                    (let ((u-orB2 (last-node)))
                      (ass) (refocus! u-orB2) (ass))            ; close or-elim subgoal(s)
                    (refocus! u-eqB))

                  ;; (= xe CHOICE) in asms.  Goal: (IN xe k-av).  Reduce via comp-mi.
                  (comp-mi)
                  (let ((u-cmiB (last-node)))
                    ;; subgoal 1: (IN xe SET) via membership-implies-sethood + (IN xe PAIR).
                    (ta 'membership-implies-sethood)
                    (inst '(FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET)))) xe)
                    (inst `(FORALL b (IMPLIES (IN ,xe b) (IN ,xe SET)))
                          `(PAIR (CHOICE ,k-av) (CHOICE ,k-av)))
                    (bc `(IMPLIES (IN ,xe (PAIR (CHOICE ,k-av) (CHOICE ,k-av))) (IN ,xe SET)))
                    (ass)
                    (refocus! u-cmiB))
                  ;; subgoal 2: (AND (IN xe Cv) (= Fv-xe av))
                  (subst `(= ,xe (CHOICE ,k-av)))               ; xe -> CHOICE in goal
                  ;; goal: (AND (IN CHOICE Cv) (= Fv-CHOICE av))
                  (di)
                  (let ((u-andB (last-node)))
                    (ass)                                       ; (IN CHOICE Cv) in asms
                    (refocus! u-andB)
                    (ass)))                                     ; close u-andB let + let* ((nXE) (xe))
                (refocus! u-keq))

              ;; (= k-av PAIR(...)) in asms.  Now (IN k-av SET) via (IN PAIR SET).
              (cut `(IN (PAIR (CHOICE ,k-av) (CHOICE ,k-av)) SET))
              (let ((u-pair-set (last-node)))
                (ta 'pairing)
                (inst '(FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET)) (IN (PAIR a b) SET))))
                      `(CHOICE ,k-av))
                (inst `(FORALL b (IMPLIES (AND (IN (CHOICE ,k-av) SET) (IN b SET))
                                           (IN (PAIR (CHOICE ,k-av) b) SET)))
                      `(CHOICE ,k-av))
                (bc `(IMPLIES (AND (IN (CHOICE ,k-av) SET) (IN (CHOICE ,k-av) SET))
                              (IN (PAIR (CHOICE ,k-av) (CHOICE ,k-av)) SET)))
                (di)
                (let ((u-ps-and (last-node)))
                  (ass) (refocus! u-ps-and) (ass))
                (refocus! u-pair-set))

              ;; subst (= k-av PAIR ...) into (IN PAIR SET) to derive (IN k-av SET).
              (subst `(= ,k-av (PAIR (CHOICE ,k-av) (CHOICE ,k-av))))
              (ass)

              (refocus! u-case-empty))

            ;;; ----- Empty case: (NOT G-a) -----
            ;; Show k-av has no elements; by class-ext, k-av = EMPTY-SET.

            (cut `(= ,k-av EMPTY-SET))
            (let ((u-keq2 (last-node)))
              (ta 'class-extensionality)
              (inst '(FORALL A (FORALL B (IMPLIES (FORALL x (IFF (IN x A) (IN x B)))
                                                   (= A B))))
                    k-av)
              (inst `(FORALL B (IMPLIES (FORALL x (IFF (IN x ,k-av) (IN x B)))
                                        (= ,k-av B)))
                    'EMPTY-SET)
              (bc `(IMPLIES (FORALL x (IFF (IN x ,k-av) (IN x EMPTY-SET)))
                            (= ,k-av EMPTY-SET)))
              (let* ((nXE2 *fresh-counter*)
                     (xe2 (eigen-name 'x nXE2)))
                (di)                    ; intro x
                (di)                    ; iff split
                (let ((u-iff-emp (last-node)))
                  ;; subgoal a: (IN xe2 k-av) -> (IN xe2 EMPTY-SET).
                  ;; iff-intro already moved (IN xe2 k-av) into asms.
                  ;; (IN xe2 k-av) gives FORSOME s ..., contradicts (NOT G-a).
                  (comp-me `(IN ,xe2 ,k-av))
                  (ai `(AND (IN ,xe2 ,Cv) (= (,Fv ,xe2) ,av)))
                  ;; (IN xe2 Cv), (= Fv-of-xe2 av) in asms.
                  ;; Contradicts (NOT G-a).  Build G-a's body and contradict.
                  (cut G-a)
                  (let ((u-ga (last-node)))
                    (ew xe2)
                    (di)
                    (let ((u-ga-and (last-node)))
                      (ass) (refocus! u-ga-and) (ass))
                    (refocus! u-ga))
                  (ai `(NOT ,G-a))
                  (refocus! u-iff-emp))
                ;; subgoal b: (IN xe2 EMPTY-SET) -> (IN xe2 k-av).
                ;; iff-intro already moved (IN xe2 EMPTY-SET) into asms.
                (ta 'empty-set-has-no-members)
                (inst '(FORALL x (NOT (IN x EMPTY-SET))) xe2)
                (ai `(NOT (IN ,xe2 EMPTY-SET))))
              (refocus! u-keq2))

            (subst `(= ,k-av EMPTY-SET))
            (ta 'empty-set-is-set)
            (ass))))                    ; close (IN EMPTY-SET SET); close case-empty; close k-av; close cases
      (refocus! u-Kset))

    (display ";;; --- Part 1: (IN K SET) proven ---\n")
    (show)

    ;; ----------------------------------------------------------------
    ;; Part 2: prove (FORALL x (IFF (IN x cls) (IN x K))).
    ;; ----------------------------------------------------------------
    (cut `(FORALL x (IFF (IN x ,Cv) (IN x ,K))))
    (let ((u-iffK (last-node)))
      (let* ((nP2 *fresh-counter*)
             (xp (eigen-name 'x nP2)))
        (di)                            ; intro x
        (di)                            ; iff split
        (let ((u-iffK-b (last-node)))
          ;; Subgoal A: (IN xp cls) in asms; goal (IN xp K).
          (bu-mi (Fv-of xp))
          (let ((u-buA (last-node)))
            ;; subgoal 1: (IN (Fv xp) Sv) -- via TOTAL.
            (inst TOTAL xp)
            (bc `(IMPLIES (IN ,xp ,Cv) (IN (,Fv ,xp) ,Sv)))
            (ass)
            (refocus! u-buA))
          ;; subgoal 2: (IN xp (COMP s (AND (IN s Cv) (= (Fv s) (Fv xp)))))
          (comp-mi)
          (let ((u-cmiA (last-node)))
            ;; (IN xp SET) via membership-implies-sethood + (IN xp Cv).
            (ta 'membership-implies-sethood)
            (inst '(FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET)))) xp)
            (inst `(FORALL b (IMPLIES (IN ,xp b) (IN ,xp SET))) Cv)
            (bc `(IMPLIES (IN ,xp ,Cv) (IN ,xp SET)))
            (ass)
            (refocus! u-cmiA))
          ;; subgoal 2: (AND (IN xp Cv) (= (Fv xp) (Fv xp)))
          (di)
          (let ((u-andA (last-node)))
            (ass)                                  ; (IN xp Cv) in asms
            (refocus! u-andA)
            (rfl))                                 ; (= (Fv xp) (Fv xp))
          (refocus! u-iffK-b))
        ;; Subgoal B: (IN xp K) in asms; goal (IN xp cls).
        (let ((nB *fresh-counter*))
          (bu-me `(IN ,xp ,K))
          (let* ((eA (eigen-name 'a nB))
                 (k-eA `(COMP s (AND (IN s ,Cv) (= (,Fv s) ,eA)))))
            (comp-me `(IN ,xp ,k-eA))
            (ai `(AND (IN ,xp ,Cv) (= (,Fv ,xp) ,eA)))
            (ass))))
      (refocus! u-iffK))

    (display ";;; --- Part 2: (FORALL x (IFF (IN x cls) (IN x K))) proven ---\n")
    (show)

    ;; ----------------------------------------------------------------
    ;; Part 3: class-extensionality gives (= cls K).
    ;; ----------------------------------------------------------------
    (cut `(= ,Cv ,K))
    (let ((u-eqCK (last-node)))
      (ta 'class-extensionality)
      (inst '(FORALL A (FORALL B (IMPLIES (FORALL x (IFF (IN x A) (IN x B)))
                                            (= A B))))
            Cv)
      (inst `(FORALL B (IMPLIES (FORALL x (IFF (IN x ,Cv) (IN x B)))
                                 (= ,Cv B)))
            K)
      (bc `(IMPLIES (FORALL x (IFF (IN x ,Cv) (IN x ,K))) (= ,Cv ,K)))
      (ass)
      (refocus! u-eqCK))

    ;; ----------------------------------------------------------------
    ;; Part 4: subst cls -> K in goal (IN cls SET) -> (IN K SET); ass.
    ;; ----------------------------------------------------------------
    (subst `(= ,Cv ,K))
    (ass)
    (display ";;; --- set-from-injection PROVEN ---\n")
    (show)))

(qed 'set-from-injection)
(display "--- set-from-injection installed ---\n")
;;;
;;; By contradiction (per user's BIG-UNION argument).  Define h(alpha) :=
;;; CHOICE(X \ wo-picks(X, alpha)).  Under (NOT FORSOME), h(alpha) in X for
;;; every alpha in ORD; injectivity follows from wo-picks-monotone.  Define
;;;   k(x) := IF (FORSOME alpha in ORD, h(alpha) = x)
;;;           THEN PAIR(CHOICE-of-witness-class, CHOICE-of-witness-class)
;;;           ELSE EMPTY-SET
;;;   K    := BIG-UNION x in X. k(x)
;;; Then K is a set, every ordinal is in K, and every element of K is an
;;; ordinal.  By class-extensionality, K = ORD; (IN K SET) then contradicts
;;; burali-forti.
;;; =======================================================================

(sp (make-wff
     '(FORALL X (IMPLIES (IN X SET)
        (FORSOME alpha (AND (IN alpha ORD)
                            (FORALL z (IMPLIES (IN z X) (IN z (wo-picks X alpha))))))))))

(let* ((nE0 *fresh-counter*)
       (Xv  (eigen-name 'X nE0)))
  (di)                                  ; intro X (with IN X SET bound)
  (pbc)                                 ; assume (NOT FORSOME); goal FALSITY

  ;; Step 3.1: derive (FORALL alpha in ORD, X not-subset wo-picks(X, alpha)).
  (cut `(FORALL alpha (IMPLIES (IN alpha ORD)
            (NOT (FORALL z (IMPLIES (IN z ,Xv) (IN z (wo-picks ,Xv alpha))))))))
  (let ((u-every-not (last-node)))
    (let* ((nE1 *fresh-counter*)
           (alpha-pf (eigen-name 'alpha nE1)))
      (di)
      (di)                              ; intros (FORALL z ...) as asm; goal FALSITY
      (cut `(FORSOME alpha (AND (IN alpha ORD)
                                (FORALL z (IMPLIES (IN z ,Xv) (IN z (wo-picks ,Xv alpha)))))))
      (let ((u-fs (last-node)))
        (ew alpha-pf)
        (di)
        (let ((u-and (last-node)))
          (ass)
          (refocus! u-and)
          (ass))
        (refocus! u-fs))
      (ai `(NOT (FORSOME alpha (AND (IN alpha ORD)
                                    (FORALL z (IMPLIES (IN z ,Xv) (IN z (wo-picks ,Xv alpha)))))))))
    (refocus! u-every-not))

  ;; Step 3.2: define K via COMP-based k(u), prove inj-lemma, K-sethood,
  ;; the IFF (IN x K) <-> (IN x ORD), then class-ext + burali-forti.
  ;;
  ;;   h(alpha) := CHOICE(X \ wo-picks(X, alpha))      -- "the pick at step alpha"
  ;;   k(u)     := COMP s (AND (IN s ORD) (= h(s) u))  -- a class (either empty or singleton)
  ;;   K        := BIG-UNION u in X. k(u)
  ;;
  ;; Under every-not-sub, h is injective on ORD (inj-lemma below).  k(u) is
  ;; then at most a singleton -- by class-ext, equal to either EMPTY-SET or
  ;; PAIR(s0, s0), hence a set.  K is then a set by big-union-sethood.
  ;; Class-ext then forces K = ORD (both classes have the same elements
  ;; under every-not-sub), contradicting burali-forti.

  (let* ((h-of (lambda (a)
                 `(CHOICE (COMPLEMENT-IN ,Xv (wo-picks ,Xv ,a)))))
         (h-alpha (h-of 'alpha))
         (h-beta  (h-of 'beta))
         (h-s     (h-of 's))
         (k-of-u `(COMP s (AND (IN s ORD) (= ,h-s u))))
         (K `(BIG-UNION u ,Xv ,k-of-u))
         (inj-stmt
          `(FORALL alpha (FORALL beta
              (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD) (= ,h-alpha ,h-beta)))
                       (= alpha beta))))))

    ;; Step 3 PAUSED here.  See notes-19.md for full strategy and remaining work.
    (display ";;; --- step 3 paused at K-construction; see notes-19.md ---\n")
    (show)))

(display "--- step 3 paused ---\n")
