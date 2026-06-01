;;; archive/proven-theorems-archive.scm
;;;
;;; Originally part of proven-theorems.scm.  Archived during the
;;; 2026-05-27 PSS-centric triage: the four intermediates below
;;; (sum-ag-congruence, ord-segment-succ-monotone, ag-mul-rearrange,
;;; sum-ag-splice-out) are pure technical machinery with no anticipated
;;; standalone use in user proofs.  Sum-ag-permutation-invariance and
;;; finsum-congruence -- the two headline results that depended on the
;;; archived intermediates -- have been PROMOTED to the PSS in
;;; theorem-library/sum-ag-permutation-invariance.scm and
;;; theorem-library/finsum-congruence.scm.  Their original proof scripts
;;; are preserved below for audit.
;;;
;;; This file is NOT loaded by load.scm.  It exists solely to preserve
;;; the original derivations.

;;; =====================================================================
;;; ARCHIVED: sum-ag-congruence  (originally proven-theorems.scm lines 297-400)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; sum-ag-congruence:  if g and gp agree on ORD-SEGMENT(m), the two
;;; abelian-group sums agree:  SUM-AG(ag,g,m) = SUM-AG(ag,gp,m).
;;;
;;; NN induction on m.  Base: both sums reduce to E(ag) by sum-ag-zero.
;;; Step: sum-ag-succ exposes  (MUL ag)(SUM-AG(..,m), f(m));  the IH gives
;;; the sums-at-m equal (Fact A) and the agreement hypothesis at i = m gives
;;; f(m) equal (Fact B).  Fact A discharges the IH's four antecedents with a
;;; cut-chain, since bc peels one antecedent at a time.
;;; Prerequisite for the sum-ag-splice-out step case.

(prove-and-install! 'sum-ag-congruence
  (lambda ()
    (sp (make-wff
         '(FORALL m (IMPLIES (IN m NN)
            (FORALL ag (FORALL g (FORALL gp
              (IMPLIES (IS-ABELIAN-GROUP ag)
              (IMPLIES (IN g (FUN NN (A ag)))
              (IMPLIES (IN gp (FUN NN (A ag)))
              (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT m)) (= (g i) (gp i))))
                       (= (SUM-AG ag g m) (SUM-AG ag gp m)))))))))))))
    (ni)
    ;; base case m = 0: both sums -> E(ag)
    (di) (di) (di) (di) (di)
    (mac 'sum-ag-zero)
    (rfl)
    ;; step case m -> succ m
    (let* ((c0  *fresh-counter*)
           (mv  (eigen-name 'm  c0))
           (agv (eigen-name 'ag (+ c0 1)))
           (gv  (eigen-name 'g  (+ c0 2)))
           (gpv (eigen-name 'gp (+ c0 3)))
           (IH  `(FORALL ag (FORALL g (FORALL gp
                   (IMPLIES (IS-ABELIAN-GROUP ag)
                   (IMPLIES (IN g (FUN NN (A ag)))
                   (IMPLIES (IN gp (FUN NN (A ag)))
                   (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (g i) (gp i))))
                            (= (SUM-AG ag g ,mv) (SUM-AG ag gp ,mv))))))))))
           (IH1 `(FORALL g (FORALL gp
                   (IMPLIES (IS-ABELIAN-GROUP ,agv)
                   (IMPLIES (IN g (FUN NN (A ,agv)))
                   (IMPLIES (IN gp (FUN NN (A ,agv)))
                   (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (g i) (gp i))))
                            (= (SUM-AG ,agv g ,mv) (SUM-AG ,agv gp ,mv)))))))))
           (IH2 `(FORALL gp
                   (IMPLIES (IS-ABELIAN-GROUP ,agv)
                   (IMPLIES (IN ,gv (FUN NN (A ,agv)))
                   (IMPLIES (IN gp (FUN NN (A ,agv)))
                   (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (,gv i) (gp i))))
                            (= (SUM-AG ,agv ,gv ,mv) (SUM-AG ,agv gp ,mv))))))))
           (A1 `(IS-ABELIAN-GROUP ,agv))
           (A2 `(IN ,gv  (FUN NN (A ,agv))))
           (A3 `(IN ,gpv (FUN NN (A ,agv))))
           (A4 `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv))
                                   (= (,gv i) (,gpv i)))))
           (EQ `(= (SUM-AG ,agv ,gv ,mv) (SUM-AG ,agv ,gpv ,mv)))
           (H4 `(IMPLIES ,A4 ,EQ))
           (H3 `(IMPLIES ,A3 ,H4))
           (H2 `(IMPLIES ,A2 ,H3))
           (Hfull `(IMPLIES ,A1 ,H2))
           (Hagree `(FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,mv)))
                                       (= (,gv i) (,gpv i)))))
           (factA EQ)
           (factB `(= (,gv ,mv) (,gpv ,mv))))
      (di) (di) (di) (di) (di) (di) (di)
      (mac 'sum-ag-succ)
      ;; Fact A:  SUM-AG(ag,g,m) = SUM-AG(ag,gp,m), via the IH
      (cut factA)
      (let ((use-factA (last-node)))
        (inst IH agv) (inst IH1 gv) (inst IH2 gpv)
        (cut H2)
        (let ((use-H2 (last-node)))
          (bc Hfull) (ass) (refocus! use-H2)
          (cut H3)
          (let ((use-H3 (last-node)))
            (bc H2) (ass) (refocus! use-H3)
            (cut H4)
            (let ((use-H4 (last-node)))
              (bc H3) (ass) (refocus! use-H4)
              (bc H4)                       ; goal -> A4
              (let ((iv (eigen-name 'i *fresh-counter*)))
                (di)                        ; intro i, assume i in ord-segment(m)
                (inst Hagree iv)
                (bc `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,mv)))
                              (= (,gv ,iv) (,gpv ,iv))))
                (mac 'ord-segment-nn-succ)
                (oi-l)
                (ass)))))
        (refocus! use-factA)
        ;; Fact B:  g(m) = gp(m), via the agreement hypothesis at i = m
        (cut factB)
        (let ((use-factB (last-node)))
          (inst Hagree mv)
          (bc `(IMPLIES (IN ,mv (ORD-SEGMENT (succ ,mv)))
                        (= (,gv ,mv) (,gpv ,mv))))
          (mac 'ord-segment-nn-succ)
          (oi-r)
          (rfl)
          (refocus! use-factB)
          ;; combine: rewrite both sums and both function values
          (subst factA)
          (subst factB)
          (rfl))))))


;;; =====================================================================
;;; ARCHIVED: ord-segment-succ-monotone  (originally proven-theorems.scm lines 401-457)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; ord-segment-succ-monotone:  n in NN => for i in os(n), succ i in os(succ n).
;;; NN induction on n; dev file prover/scratch-succmono.scm.
;;; -----------------------------------------------------------------------
(prove-and-install! 'ord-segment-succ-monotone
  (lambda ()
    (sp (make-wff
         '(FORALL n (IMPLIES (IN n NN)
            (FORALL i (IMPLIES (IN i (ORD-SEGMENT n))
              (IN (succ i) (ORD-SEGMENT (succ n)))))))))
    (ni)

    (let ((i0 (eigen-name 'i *fresh-counter*)))
      (di)
      (ta 'ord-segment-zero-no-members)
      (inst '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))) i0)
      (ai `(NOT (IN ,i0 (ORD-SEGMENT 0)))))

    (let ((nv (eigen-name 'n *fresh-counter*)))
      (di)                           ; intro n, assume n in NN
      (di)                           ; assume IH
      (cut `(IN (succ ,nv) NN))
      (let ((use-snn (last-node)))
        (ta 'nn-succ-closed)
        (inst '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))) nv)
        (bc `(IMPLIES (IN ,nv NN) (IN (succ ,nv) NN)))
        (ass)
        (refocus! use-snn))
      (let ((iv (eigen-name 'i *fresh-counter*)))
        (di)                         ; intro i, assume i in ORD-SEGMENT(succ n)
        (cut `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,nv)))
                       (IN (succ ,iv) (ORD-SEGMENT (succ (succ ,nv))))))
        (let ((use-imp (last-node)))
          ;; one mac rewrites antecedent i in os(succ n) AND goal succ i in
          ;; os(succ(succ n)) into OR-form.
          (mac 'ord-segment-nn-succ)
          (di)                       ; assume (OR i in os(n), i = n)
          (ai `(OR (IN ,iv (ORD-SEGMENT ,nv)) (= ,iv ,nv)))
          (let ((case2 (last-node)))
            ;; case 1: i in ORD-SEGMENT(n) -- use the IH
            (oi-l)                   ; goal -> (IN (succ i) (ORD-SEGMENT (succ n)))
            (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv))
                                      (IN (succ i) (ORD-SEGMENT (succ ,nv))))) iv)
            (bc `(IMPLIES (IN ,iv (ORD-SEGMENT ,nv))
                          (IN (succ ,iv) (ORD-SEGMENT (succ ,nv)))))
            (ass)
            ;; case 2: i = n
            (refocus! case2)
            (subst `(= ,iv ,nv))     ; goal OR-form, rewrite i -> n
            (oi-r)
            (rfl))
          (refocus! use-imp)
          (bc `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,nv)))
                        (IN (succ ,iv) (ORD-SEGMENT (succ (succ ,nv))))))
          (ass))))
))


;;; =====================================================================
;;; ARCHIVED: ag-mul-rearrange  (originally proven-theorems.scm lines 458-580)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; ag-mul-rearrange:  in an abelian group,  (a*b)*c = (a*c)*b.
;;;
;;; group-assoc reassociates each side, abelian-group-mul-comm swaps b,c.
;;; group-assoc's macete form cannot fire (its source ((MUL s)(..)..) has a
;;; compound head, which match-expr cannot match), so it is applied the long
;;; way: ta + inst + cut-chain + subst.  Likewise this lemma is for ta/inst
;;; use, not as a rewrite macete.

(prove-and-install! 'ag-mul-rearrange
  (lambda ()
    (sp (make-wff
         '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
            (FORALL a (IMPLIES (IN a (A ag))
              (FORALL b (IMPLIES (IN b (A ag))
                (FORALL c (IMPLIES (IN c (A ag))
                  (= ((MUL ag) ((MUL ag) a b) c)
                     ((MUL ag) ((MUL ag) a c) b))))))))))))
    (let* ((rc   *fresh-counter*)
           (ragv (eigen-name 'ag rc))
           (rav  (eigen-name 'a (+ rc 1)))
           (rbv  (eigen-name 'b (+ rc 2)))
           (rcv  (eigen-name 'c (+ rc 3)))
           (ga '(FORALL s (IMPLIES (IS-GROUP s)
                  (FORALL a (IMPLIES (IN a (A s))
                    (FORALL b (IMPLIES (IN b (A s))
                      (FORALL c (IMPLIES (IN c (A s))
                        (= ((MUL s) ((MUL s) a b) c)
                           ((MUL s) a ((MUL s) b c))))))))))))
           (ga-Fa
             `(FORALL a (IMPLIES (IN a (A ,ragv))
                (FORALL b (IMPLIES (IN b (A ,ragv))
                  (FORALL c (IMPLIES (IN c (A ,ragv))
                    (= ((MUL ,ragv) ((MUL ,ragv) a b) c)
                       ((MUL ,ragv) a ((MUL ,ragv) b c))))))))))
           (ga-imp `(IMPLIES (IS-GROUP ,ragv) ,ga-Fa))
           (ga-Fb1
             `(FORALL b (IMPLIES (IN b (A ,ragv))
                (FORALL c (IMPLIES (IN c (A ,ragv))
                  (= ((MUL ,ragv) ((MUL ,ragv) ,rav b) c)
                     ((MUL ,ragv) ,rav ((MUL ,ragv) b c))))))))
           (ga-Fc1
             `(FORALL c (IMPLIES (IN c (A ,ragv))
                (= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rbv) c)
                   ((MUL ,ragv) ,rav ((MUL ,ragv) ,rbv c))))))
           (eq1
             `(= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rbv) ,rcv)
                 ((MUL ,ragv) ,rav ((MUL ,ragv) ,rbv ,rcv))))
           (ga-Fc2
             `(FORALL c (IMPLIES (IN c (A ,ragv))
                (= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rcv) c)
                   ((MUL ,ragv) ,rav ((MUL ,ragv) ,rcv c))))))
           (eq2
             `(= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rcv) ,rbv)
                 ((MUL ,ragv) ,rav ((MUL ,ragv) ,rcv ,rbv))))
           (agc '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
                   (FORALL a (IMPLIES (IN a (A s))
                     (FORALL b (IMPLIES (IN b (A s))
                       (= ((MUL s) a b) ((MUL s) b a)))))))))
           (agc-Fa
             `(FORALL a (IMPLIES (IN a (A ,ragv))
                (FORALL b (IMPLIES (IN b (A ,ragv))
                  (= ((MUL ,ragv) a b) ((MUL ,ragv) b a)))))))
           (agc-Fb
             `(FORALL b (IMPLIES (IN b (A ,ragv))
                (= ((MUL ,ragv) ,rbv b) ((MUL ,ragv) b ,rbv)))))
           (eqc `(= ((MUL ,ragv) ,rbv ,rcv) ((MUL ,ragv) ,rcv ,rbv))))
      (di) (di) (di) (di) (di)        ; peel ag/IS-AG and a,b,c/inA
      ;; IS-GROUP(ag)
      (cut `(IS-GROUP ,ragv))
      (let ((u-isg (last-node)))
        (ta 'abelian-group-is-group)
        (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) ragv)
        (bc `(IMPLIES (IS-ABELIAN-GROUP ,ragv) (IS-GROUP ,ragv)))
        (ass)
        (refocus! u-isg))
      ;; assoc1:  (a*b)*c = a*(b*c)
      (ta 'group-assoc)
      (inst ga ragv)
      (cut ga-Fa)
      (let ((u1 (last-node))) (bc ga-imp) (ass) (refocus! u1))
      (inst ga-Fa rav)
      (cut ga-Fb1)
      (let ((u2 (last-node)))
        (bc `(IMPLIES (IN ,rav (A ,ragv)) ,ga-Fb1)) (ass) (refocus! u2))
      (inst ga-Fb1 rbv)
      (cut ga-Fc1)
      (let ((u3 (last-node)))
        (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,ga-Fc1)) (ass) (refocus! u3))
      (inst ga-Fc1 rcv)
      (cut eq1)
      (let ((u4 (last-node)))
        (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,eq1)) (ass) (refocus! u4))
      ;; assoc2:  (a*c)*b = a*(c*b)   (reuse ga-Fa, ga-Fb1)
      (inst ga-Fb1 rcv)
      (cut ga-Fc2)
      (let ((u5 (last-node)))
        (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,ga-Fc2)) (ass) (refocus! u5))
      (inst ga-Fc2 rbv)
      (cut eq2)
      (let ((u6 (last-node)))
        (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,eq2)) (ass) (refocus! u6))
      ;; comm:  b*c = c*b
      (ta 'abelian-group-mul-comm)
      (inst agc ragv)
      (cut agc-Fa)
      (let ((u7 (last-node)))
        (bc `(IMPLIES (IS-ABELIAN-GROUP ,ragv) ,agc-Fa)) (ass) (refocus! u7))
      (inst agc-Fa rbv)
      (cut agc-Fb)
      (let ((u8 (last-node)))
        (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,agc-Fb)) (ass) (refocus! u8))
      (inst agc-Fb rcv)
      (cut eqc)
      (let ((u9 (last-node)))
        (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,eqc)) (ass) (refocus! u9))
      ;; finish
      (subst eq1)                     ; LHS  (a*b)*c -> a*(b*c)
      (subst eq2)                     ; RHS  (a*c)*b -> a*(c*b)
      (subst eqc)                     ; a*(b*c) -> a*(c*b)
      (rfl))))



;;; =====================================================================
;;; ARCHIVED: sum-ag-splice-out  (originally proven-theorems.scm lines 581-1151)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; sum-ag-splice-out:  removing index k from a finite abelian-group sum.
;;; Proof developed in prover/scratch-perm.scm; see that file for the
;;; checkpointed transcript.  NN induction; step case splits k via
;;; ord-segment-nn-succ into k<succ n (IH, caseA) and k=succ n (caseB).
;;; -----------------------------------------------------------------------
(prove-and-install! 'sum-ag-splice-out
  (lambda ()

(define splice-goal
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (FORALL g (FORALL k (FORALL gp
       (IMPLIES (IS-ABELIAN-GROUP ag)
       (IMPLIES (IN g (FUN NN (A ag)))
       (IMPLIES (IN gp (FUN NN (A ag)))
       (IMPLIES (IN k (ORD-SEGMENT (succ n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k))
                                   (= (gp i) (g i))))
       (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT n))
                                        (NOT (IN i (ORD-SEGMENT k))))
                                   (= (gp i) (g (succ i)))))
         (= (SUM-AG ag g (succ n))
            ((MUL ag) (SUM-AG ag gp n) (g k))))))))))))))))

(define (eigen h n)
  (string->symbol (string-append (symbol->string h) "_" (number->string n))))

(sp (make-wff splice-goal))
(ni)
(display "--- after (ni) ---\n") (show)

;;; ===== BASE CASE  n = 0 =====
(define bv *fresh-counter*)
(define agv (eigen 'ag bv))
(define gv  (eigen 'g  (+ bv 1)))
(define kv  (eigen 'k  (+ bv 2)))
(define gpv (eigen 'gp (+ bv 3)))

(di)                 ; peel forall ag,g,k,gp
(di) (di) (di)       ; assume is-abelian-group(ag), g in fun, gp in fun
(ta 'nn-zero-in)     ; 0 in nn  -- discharges macete side-conditions
(mac 'ord-segment-nn-succ)        ; k in ord-segment(succ 0) -> OR(in ord-seg 0, = 0)
(display "--- base: after mac ord-segment-nn-succ ---\n") (show)
(di)                 ; assume  k in ord-segment(0) or k = 0
(ai `(OR (IN ,kv (ORD-SEGMENT 0)) (= ,kv 0)))
;; ai's OR-elim leaves two sibling goals; the k=0 case is the last node.
(define caseB (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(display "--- base: after (ai) case split ---\n") (show)

;;; --- case A: k in ord-segment(0) -- impossible ---
(ta 'ord-segment-zero-no-members)
(inst '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))) kv)
(ai `(NOT (IN ,kv (ORD-SEGMENT 0))))
(display "--- base: after killing case A ---\n") (show)

;;; --- case B: k = 0 ---
(set-proof-state-focus! *ps* caseB)
(di) (di)            ; assume the two agreement hypotheses
(subst `(= ,kv 0))   ; rewrite k -> 0 in the goal
(display "--- base B: after subst k=0 ---\n") (show)
(mac 'sum-ag-succ)   ; sum-ag(ag,g,succ 0) -> (mul ag)(sum-ag(ag,g,0), g(0))
(mac 'sum-ag-zero)   ; sum-ag(ag,_,0) -> E(ag)
(display "--- base B: after sum-ag reductions ---\n") (show)
(rfl)
(display "--- base B: after rfl ---\n") (show)

;;; ===== STEP CASE  n -> succ n =====
;;; Focus auto-advanced to the step node [2] after the base case closed.
;;; Step node:  forall([n in nn], INNER(n) implies INNER(succ n)).
(display "--- step case in focus ---\n") (show)

(define sv *fresh-counter*)
(define snv  (eigen 'n  sv))          ; eigen n
(define sagv (eigen 'ag (+ sv 1)))
(define sgv  (eigen 'g  (+ sv 2)))
(define skv  (eigen 'k  (+ sv 3)))
(define sgpv (eigen 'gp (+ sv 4)))

(di)                 ; intro n, hyp n in nn
(di)                 ; assume IH = INNER(n)
(di)                 ; peel forall ag,g,k,gp
(di) (di) (di)       ; assume is-abelian-group(ag), g in fun, gp in fun
(display "--- step: after peeling to k-membership antecedent ---\n") (show)

;;; ord-segment-nn-succ needs  succ n in NN  as a side condition; cut it in.
(cut `(IN (succ ,snv) NN))
(define use-succ-nn (last-node))
  (ta 'nn-succ-closed)
  (inst '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))) snv)
  (bc `(IMPLIES (IN ,snv NN) (IN (succ ,snv) NN)))
  (ass)
(refocus! use-succ-nn)
(display "--- step: succ n in NN established ---\n") (show)

;;; rewrite the  k in ORD-SEGMENT(succ(succ n))  antecedent, then split.
(mac 'ord-segment-nn-succ)
(di)                 ; assume  k in ord-segment(succ n)  or  k = succ n
(ai `(OR (IN ,skv (ORD-SEGMENT (succ ,snv))) (= ,skv (succ ,snv))))
(define step-caseB (car  (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define step-caseA (cadr (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(display "--- step: after case split (caseA + caseB captured) ---\n") (show)

;;; =======================================================================
;;; STEP caseB:  k = succ n   --  splice removes the last index.
;;;
;;; AGREE1 says g, gp agree on ord-segment(k) = ord-segment(succ n), so the
;;; two sums over succ n are equal (sum-ag-congruence); sum-ag-succ then
;;; peels the last term off each side.
;;; =======================================================================
(set-proof-state-focus! *ps* step-caseB)
(di) (di)            ; assume AGREE1, AGREE2'
(subst `(= ,skv (succ ,snv)))   ; rewrite k -> succ n in the goal
(display "--- caseB: goal after subst k=succ n ---\n") (show)

;;; --- clean agreement: agree1p = forall i in os(succ n). g(i)=gp(i) ---
;;; AGREE1 (hyp) is over os(k) with orientation gp(i)=g(i); rebuild it over
;;; os(succ n) with orientation g(i)=gp(i), the form sum-ag-congruence wants.
(define agree1p
  `(FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,snv))) (= (,sgv i) (,sgpv i)))))
(cut agree1p)
(define use-agree1p (last-node))
  (define civ *fresh-counter*)
  (define iv (eigen 'i civ))
  (di)                            ; intro i, assume i in os(succ n)
  (cut `(IN ,iv (ORD-SEGMENT ,skv)))
  (define use-iink (last-node))
    (subst `(= ,skv (succ ,snv)))  ; (IN i os(k)) -> (IN i os(succ n))
    (ass)
  (refocus! use-iink)
  (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,skv)) (= (,sgpv i) (,sgv i)))) iv)
  (cut `(= (,sgpv ,iv) (,sgv ,iv)))
  (define use-flip (last-node))
    (bc `(IMPLIES (IN ,iv (ORD-SEGMENT ,skv)) (= (,sgpv ,iv) (,sgv ,iv))))
    (ass)
  (refocus! use-flip)
  (subst `(= (,sgpv ,iv) (,sgv ,iv)))   ; (= g(i) gp(i)) -> (= g(i) g(i))
  (rfl)
(refocus! use-agree1p)
(display "--- caseB: agree1p established ---\n") (show)

;;; --- FACT-C:  sum-ag(g,succ n) = sum-ag(gp,succ n)  via sum-ag-congruence ---
(define factC
  `(= (SUM-AG ,sagv ,sgv (succ ,snv)) (SUM-AG ,sagv ,sgpv (succ ,snv))))
(define congrT
  '(FORALL m (IMPLIES (IN m NN)
     (FORALL ag (FORALL g (FORALL gp
       (IMPLIES (IS-ABELIAN-GROUP ag)
       (IMPLIES (IN g (FUN NN (A ag)))
       (IMPLIES (IN gp (FUN NN (A ag)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT m)) (= (g i) (gp i))))
                (= (SUM-AG ag g m) (SUM-AG ag gp m))))))))))))
(define congr-T1c
  `(FORALL ag (FORALL g (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ag)
     (IMPLIES (IN g (FUN NN (A ag)))
     (IMPLIES (IN gp (FUN NN (A ag)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,snv))) (= (g i) (gp i))))
              (= (SUM-AG ag g (succ ,snv)) (SUM-AG ag gp (succ ,snv)))))))))))
(define congr-T2
  `(FORALL g (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,sagv)
     (IMPLIES (IN g (FUN NN (A ,sagv)))
     (IMPLIES (IN gp (FUN NN (A ,sagv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,snv))) (= (g i) (gp i))))
              (= (SUM-AG ,sagv g (succ ,snv)) (SUM-AG ,sagv gp (succ ,snv))))))))))
(define congr-T3
  `(FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,sagv)
     (IMPLIES (IN ,sgv (FUN NN (A ,sagv)))
     (IMPLIES (IN gp (FUN NN (A ,sagv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,snv))) (= (,sgv i) (gp i))))
              (= (SUM-AG ,sagv ,sgv (succ ,snv)) (SUM-AG ,sagv gp (succ ,snv)))))))))
(define cB-isag `(IS-ABELIAN-GROUP ,sagv))
(define cB-gfun `(IN ,sgv  (FUN NN (A ,sagv))))
(define cB-gpfun `(IN ,sgpv (FUN NN (A ,sagv))))
(define cB-T4d `(IMPLIES ,agree1p ,factC))
(define cB-T4c `(IMPLIES ,cB-gpfun ,cB-T4d))
(define cB-T4b `(IMPLIES ,cB-gfun ,cB-T4c))
(define cB-T4  `(IMPLIES ,cB-isag ,cB-T4b))

(cut factC)
(define use-factC (last-node))
  (ta 'sum-ag-congruence)
  (inst congrT `(succ ,snv))
  (cut congr-T1c)
  (define use-T1c (last-node))
    (bc `(IMPLIES (IN (succ ,snv) NN) ,congr-T1c))
    (ass)
  (refocus! use-T1c)
  (inst congr-T1c sagv)
  (inst congr-T2  sgv)
  (inst congr-T3  sgpv)
  (cut cB-T4b) (define use-cB-T4b (last-node)) (bc cB-T4)  (ass) (refocus! use-cB-T4b)
  (cut cB-T4c) (define use-cB-T4c (last-node)) (bc cB-T4b) (ass) (refocus! use-cB-T4c)
  (cut cB-T4d) (define use-cB-T4d (last-node)) (bc cB-T4c) (ass) (refocus! use-cB-T4d)
  (bc cB-T4d)              ; goal -> agree1p
  (ass)
(refocus! use-factC)
(display "--- caseB: FACT-C established ---\n") (show)

;;; --- combine ---
(mac 'sum-ag-succ)        ; both succ-sums peeled
(subst factC)             ; sum-ag(g,succ n) -> sum-ag(gp,succ n)
(mac 'sum-ag-succ)        ; peel the reintroduced sum-ag(gp,succ n)
(rfl)
(display "--- caseB: DONE ---\n") (show)

;;; =======================================================================
;;; STEP caseA:  k in ORD-SEGMENT(succ n)   --  the spliced index k <= n.
;;;
;;;   sum-ag-succ peels  g(succ n)  off the LHS sum;
;;;   the IH at index n rewrites the remaining SUM-AG(g, succ n);
;;;   AGREE2' at i = n turns gp(n) into g(succ n);
;;;   an abelian rearrangement (assoc + comm) finishes.
;;; =======================================================================
(set-proof-state-focus! *ps* step-caseA)
(di) (di)            ; assume AGREE1, AGREE2'
(display "--- caseA: goal after assuming AGREE1, AGREE2' ---\n") (show)

;;; ---- formula abbreviations -------------------------------------------
(define cA-A1 `(IS-ABELIAN-GROUP ,sagv))
(define cA-A2 `(IN ,sgv  (FUN NN (A ,sagv))))
(define cA-A3 `(IN ,sgpv (FUN NN (A ,sagv))))
(define cA-A4 `(IN ,skv  (ORD-SEGMENT (succ ,snv))))
(define cA-AGREE1                       ; assumed hyp
  `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,skv)) (= (,sgpv i) (,sgv i)))))
(define cA-AGREE2p           ; assumed AGREE2' -- mac already rewrote os(succ n)
  `(FORALL i (IMPLIES (AND (OR (IN i (ORD-SEGMENT ,snv)) (= i ,snv))
                           (NOT (IN i (ORD-SEGMENT ,skv))))
                      (= (,sgpv i) (,sgv (succ i))))))
(define cA-AGREE2n                      ; the IH's AGREE, over os(n)
  `(FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT ,snv))
                           (NOT (IN i (ORD-SEGMENT ,skv))))
                      (= (,sgpv i) (,sgv (succ i))))))
(define cA-factIH
  `(= (SUM-AG ,sagv ,sgv (succ ,snv))
      ((MUL ,sagv) (SUM-AG ,sagv ,sgpv ,snv) (,sgv ,skv))))
(define cA-factGP `(= (,sgpv ,snv) (,sgv (succ ,snv))))

;;; the induction hypothesis (INNER at index n)
(define cA-IH
  `(FORALL ag (FORALL g (FORALL k (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ag)
     (IMPLIES (IN g (FUN NN (A ag)))
     (IMPLIES (IN gp (FUN NN (A ag)))
     (IMPLIES (IN k (ORD-SEGMENT (succ ,snv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k)) (= (gp i) (g i))))
     (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT ,snv))
                                      (NOT (IN i (ORD-SEGMENT k))))
                                 (= (gp i) (g (succ i)))))
       (= (SUM-AG ag g (succ ,snv))
          ((MUL ag) (SUM-AG ag gp ,snv) (g k))))))))))))))
(define cA-ih1                          ; ag := sagv
  `(FORALL g (FORALL k (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,sagv)
     (IMPLIES (IN g (FUN NN (A ,sagv)))
     (IMPLIES (IN gp (FUN NN (A ,sagv)))
     (IMPLIES (IN k (ORD-SEGMENT (succ ,snv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k)) (= (gp i) (g i))))
     (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT ,snv))
                                      (NOT (IN i (ORD-SEGMENT k))))
                                 (= (gp i) (g (succ i)))))
       (= (SUM-AG ,sagv g (succ ,snv))
          ((MUL ,sagv) (SUM-AG ,sagv gp ,snv) (g k)))))))))))))
(define cA-ih2                          ; g := sgv
  `(FORALL k (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,sagv)
     (IMPLIES (IN ,sgv (FUN NN (A ,sagv)))
     (IMPLIES (IN gp (FUN NN (A ,sagv)))
     (IMPLIES (IN k (ORD-SEGMENT (succ ,snv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k)) (= (gp i) (,sgv i))))
     (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT ,snv))
                                      (NOT (IN i (ORD-SEGMENT k))))
                                 (= (gp i) (,sgv (succ i)))))
       (= (SUM-AG ,sagv ,sgv (succ ,snv))
          ((MUL ,sagv) (SUM-AG ,sagv gp ,snv) (,sgv k))))))))))))
(define cA-ih3                          ; k := skv
  `(FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,sagv)
     (IMPLIES (IN ,sgv (FUN NN (A ,sagv)))
     (IMPLIES (IN gp (FUN NN (A ,sagv)))
     (IMPLIES (IN ,skv (ORD-SEGMENT (succ ,snv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,skv)) (= (gp i) (,sgv i))))
     (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT ,snv))
                                      (NOT (IN i (ORD-SEGMENT ,skv))))
                                 (= (gp i) (,sgv (succ i)))))
       (= (SUM-AG ,sagv ,sgv (succ ,snv))
          ((MUL ,sagv) (SUM-AG ,sagv gp ,snv) (,sgv ,skv)))))))))))
(define cA-T6 `(IMPLIES ,cA-AGREE2n ,cA-factIH))
(define cA-T5 `(IMPLIES ,cA-AGREE1  ,cA-T6))
(define cA-T4 `(IMPLIES ,cA-A4 ,cA-T5))
(define cA-T3 `(IMPLIES ,cA-A3 ,cA-T4))
(define cA-T2 `(IMPLIES ,cA-A2 ,cA-T3))
(define cA-ih4 `(IMPLIES ,cA-A1 ,cA-T2))   ; = inst of cA-ih3 at gp := sgpv

;;; ---- FACT-IH:  SUM-AG(g,succ n) = MUL(SUM-AG(gp,n), g(k)) -------------
(cut cA-factIH)
(define use-cA-factIH (last-node))
  (inst cA-IH  sagv)
  (inst cA-ih1 sgv)
  (inst cA-ih2 skv)
  (inst cA-ih3 sgpv)             ; cA-ih4 now in assumptions
  (cut cA-T2) (define u-cA-T2 (last-node)) (bc cA-ih4) (ass) (refocus! u-cA-T2)
  (cut cA-T3) (define u-cA-T3 (last-node)) (bc cA-T2)  (ass) (refocus! u-cA-T3)
  (cut cA-T4) (define u-cA-T4 (last-node)) (bc cA-T3)  (ass) (refocus! u-cA-T4)
  (cut cA-T5) (define u-cA-T5 (last-node)) (bc cA-T4)  (ass) (refocus! u-cA-T5)
  (cut cA-T6) (define u-cA-T6 (last-node)) (bc cA-T5)  (ass) (refocus! u-cA-T6)
  (bc cA-T6)                     ; goal cA-factIH -> cA-AGREE2n
  ;; derive AGREE2n (over os(n)) from AGREE2' (over os(succ n))
  (define cA-ci *fresh-counter*)
  (define cA-iv (eigen 'i cA-ci))
  (di)                           ; intro i
  (di)                           ; assume (AND i in os(n), i notin os(k))
  (ai `(AND (IN ,cA-iv (ORD-SEGMENT ,snv))
            (NOT (IN ,cA-iv (ORD-SEGMENT ,skv)))))
  (inst cA-AGREE2p cA-iv)
  (bc `(IMPLIES (AND (OR (IN ,cA-iv (ORD-SEGMENT ,snv)) (= ,cA-iv ,snv))
                     (NOT (IN ,cA-iv (ORD-SEGMENT ,skv))))
                (= (,sgpv ,cA-iv) (,sgv (succ ,cA-iv)))))
  (di)                           ; split the AND goal
  (define cA-and2 (last-node))
    (oi-l)                       ; goal1 (OR i in os(n), i = n) -> (IN i os(n))
    (ass)
  (refocus! cA-and2)
    (ass)                        ; goal2 i notin os(k)
(refocus! use-cA-factIH)
(display "--- caseA: FACT-IH established ---\n") (show)

;;; ---- typing facts ----------------------------------------------------
;;; IS-GROUP(ag)
(cut `(IS-GROUP ,sagv))
(define use-cA-isg (last-node))
  (ta 'abelian-group-is-group)
  (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) sagv)
  (bc `(IMPLIES (IS-ABELIAN-GROUP ,sagv) (IS-GROUP ,sagv)))
  (ass)
(refocus! use-cA-isg)

;;; k in NN  (via ord-segment-nn-subset)
(cut `(IN ,skv NN))
(define use-cA-knn (last-node))
  (ta 'ord-segment-nn-subset)
  (inst '(FORALL m (IMPLIES (IN m NN)
            (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN)))))
        `(succ ,snv))
  (cut `(FORALL k (IMPLIES (IN k (ORD-SEGMENT (succ ,snv))) (IN k NN))))
  (define use-cA-knn2 (last-node))
    (bc `(IMPLIES (IN (succ ,snv) NN)
            (FORALL k (IMPLIES (IN k (ORD-SEGMENT (succ ,snv))) (IN k NN)))))
    (ass)
  (refocus! use-cA-knn2)
  (inst `(FORALL k (IMPLIES (IN k (ORD-SEGMENT (succ ,snv))) (IN k NN))) skv)
  (bc `(IMPLIES (IN ,skv (ORD-SEGMENT (succ ,snv))) (IN ,skv NN)))
  (ass)
(refocus! use-cA-knn)

;;; g(k) in A(ag)  (via fun-apply-type)
(cut `(IN (,sgv ,skv) (A ,sagv)))
(define use-cA-gk (last-node))
  (ta 'fun-apply-type)
  (inst '(FORALL f (FORALL A (FORALL B (FORALL x
            (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) sgv)
  (inst `(FORALL A (FORALL B (FORALL x
            (IMPLIES (AND (IN ,sgv (FUN A B)) (IN x A)) (IN (,sgv x) B))))) 'NN)
  (inst `(FORALL B (FORALL x
            (IMPLIES (AND (IN ,sgv (FUN NN B)) (IN x NN)) (IN (,sgv x) B))))
        `(A ,sagv))
  (inst `(FORALL x (IMPLIES (AND (IN ,sgv (FUN NN (A ,sagv))) (IN x NN))
                            (IN (,sgv x) (A ,sagv)))) skv)
  (bc `(IMPLIES (AND (IN ,sgv (FUN NN (A ,sagv))) (IN ,skv NN))
                (IN (,sgv ,skv) (A ,sagv))))
  (di)                           ; split the AND goal
  (define cA-gk2 (last-node))
    (ass)                        ; g in FUN(NN,A(ag))
  (refocus! cA-gk2)
    (ass)                        ; k in NN
(refocus! use-cA-gk)

;;; g(succ n) in A(ag)  (via fun-apply-type)
(cut `(IN (,sgv (succ ,snv)) (A ,sagv)))
(define use-cA-gsn (last-node))
  (ta 'fun-apply-type)
  (inst '(FORALL f (FORALL A (FORALL B (FORALL x
            (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) sgv)
  (inst `(FORALL A (FORALL B (FORALL x
            (IMPLIES (AND (IN ,sgv (FUN A B)) (IN x A)) (IN (,sgv x) B))))) 'NN)
  (inst `(FORALL B (FORALL x
            (IMPLIES (AND (IN ,sgv (FUN NN B)) (IN x NN)) (IN (,sgv x) B))))
        `(A ,sagv))
  (inst `(FORALL x (IMPLIES (AND (IN ,sgv (FUN NN (A ,sagv))) (IN x NN))
                            (IN (,sgv x) (A ,sagv)))) `(succ ,snv))
  (bc `(IMPLIES (AND (IN ,sgv (FUN NN (A ,sagv))) (IN (succ ,snv) NN))
                (IN (,sgv (succ ,snv)) (A ,sagv))))
  (di)
  (define cA-gsn2 (last-node))
    (ass)                        ; g in FUN(NN,A(ag))
  (refocus! cA-gsn2)
    (ass)                        ; succ n in NN
(refocus! use-cA-gsn)

;;; SUM-AG(gp,n) in A(ag)  (via sum-ag-type)
(cut `(IN (SUM-AG ,sagv ,sgpv ,snv) (A ,sagv)))
(define use-cA-S (last-node))
  (ta 'sum-ag-type)
  (inst '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
            (FORALL f (IMPLIES (IN f (FUN NN (A ag)))
              (FORALL n (IMPLIES (IN n NN) (IN (SUM-AG ag f n) (A ag))))))))
        sagv)
  (cut `(FORALL f (IMPLIES (IN f (FUN NN (A ,sagv)))
           (FORALL n (IMPLIES (IN n NN) (IN (SUM-AG ,sagv f n) (A ,sagv)))))))
  (define use-cA-S2 (last-node))
    (bc `(IMPLIES (IS-ABELIAN-GROUP ,sagv)
            (FORALL f (IMPLIES (IN f (FUN NN (A ,sagv)))
              (FORALL n (IMPLIES (IN n NN)
                (IN (SUM-AG ,sagv f n) (A ,sagv))))))))
    (ass)
  (refocus! use-cA-S2)
  (inst `(FORALL f (IMPLIES (IN f (FUN NN (A ,sagv)))
           (FORALL n (IMPLIES (IN n NN) (IN (SUM-AG ,sagv f n) (A ,sagv))))))
        sgpv)
  (cut `(FORALL n (IMPLIES (IN n NN) (IN (SUM-AG ,sagv ,sgpv n) (A ,sagv)))))
  (define use-cA-S3 (last-node))
    (bc `(IMPLIES (IN ,sgpv (FUN NN (A ,sagv)))
            (FORALL n (IMPLIES (IN n NN)
              (IN (SUM-AG ,sagv ,sgpv n) (A ,sagv))))))
    (ass)
  (refocus! use-cA-S3)
  (inst `(FORALL n (IMPLIES (IN n NN) (IN (SUM-AG ,sagv ,sgpv n) (A ,sagv)))) snv)
  (bc `(IMPLIES (IN ,snv NN) (IN (SUM-AG ,sagv ,sgpv ,snv) (A ,sagv))))
  (ass)
(refocus! use-cA-S)
(display "--- caseA: typing facts established ---\n") (show)

;;; ---- FACT-GP:  gp(n) = g(succ n)   (AGREE2' at i = n) ----------------
(cut cA-factGP)
(define use-cA-factGP (last-node))
  (inst cA-AGREE2p snv)
  (bc `(IMPLIES (AND (OR (IN ,snv (ORD-SEGMENT ,snv)) (= ,snv ,snv))
                     (NOT (IN ,snv (ORD-SEGMENT ,skv))))
                (= (,sgpv ,snv) (,sgv (succ ,snv)))))
  (di)                           ; split the AND goal
  (define cA-gp-and2 (last-node))
    ;; goal1: (OR n in os(n), n = n)
    (oi-r)
    (rfl)
  (refocus! cA-gp-and2)
    ;; goal2: n notin ORD-SEGMENT(k)  -- case-split k in os(succ n)
    (cut `(IMPLIES (IN ,skv (ORD-SEGMENT (succ ,snv)))
                   (NOT (IN ,snv (ORD-SEGMENT ,skv)))))
    (define use-cA-nk (last-node))
      (mac 'ord-segment-nn-succ) ; antecedent -> (OR k in os(n), k = n)
      (di)                       ; assume (OR k in os(n), k = n)
      (ai `(OR (IN ,skv (ORD-SEGMENT ,snv)) (= ,skv ,snv)))
      (define cA-kcase2 (last-node))
        ;; --- case k in ORD-SEGMENT(n) ---
        (di)                     ; assume n in os(k), goal FALSITY
        (ta 'ord-segment-trans)
        (inst '(FORALL m (IMPLIES (IN m NN)
                  (FORALL k (FORALL i
                    (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT m)))
                             (IN i (ORD-SEGMENT m))))))) snv)
        (cut `(FORALL k (FORALL i
                 (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT ,snv)))
                          (IN i (ORD-SEGMENT ,snv))))))
        (define use-cA-tr (last-node))
          (bc `(IMPLIES (IN ,snv NN)
                  (FORALL k (FORALL i
                    (IMPLIES (AND (IN i (ORD-SEGMENT k))
                                  (IN k (ORD-SEGMENT ,snv)))
                             (IN i (ORD-SEGMENT ,snv)))))))
          (ass)
        (refocus! use-cA-tr)
        (inst `(FORALL k (FORALL i
                  (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT ,snv)))
                           (IN i (ORD-SEGMENT ,snv))))) skv)
        (inst `(FORALL i
                  (IMPLIES (AND (IN i (ORD-SEGMENT ,skv))
                                (IN ,skv (ORD-SEGMENT ,snv)))
                           (IN i (ORD-SEGMENT ,snv)))) snv)
        (cut `(IN ,snv (ORD-SEGMENT ,snv)))
        (define use-cA-ninn (last-node))
          (bc `(IMPLIES (AND (IN ,snv (ORD-SEGMENT ,skv))
                             (IN ,skv (ORD-SEGMENT ,snv)))
                        (IN ,snv (ORD-SEGMENT ,snv))))
          (di)                   ; split the AND goal
          (define cA-tr-and2 (last-node))
            (ass)                ; n in os(k)
          (refocus! cA-tr-and2)
            (ass)                ; k in os(n)
        (refocus! use-cA-ninn)
        (ta 'ord-segment-self)
        (inst '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n))))) snv)
        (cut `(NOT (IN ,snv (ORD-SEGMENT ,snv))))
        (define use-cA-self (last-node))
          (bc `(IMPLIES (IN ,snv NN) (NOT (IN ,snv (ORD-SEGMENT ,snv)))))
          (ass)
        (refocus! use-cA-self)
        (ai `(NOT (IN ,snv (ORD-SEGMENT ,snv))))   ; closes FALSITY
      (refocus! cA-kcase2)
        ;; --- case k = n ---
        (subst `(= ,skv ,snv))   ; (NOT (IN n os(k))) -> (NOT (IN n os(n)))
        (ta 'ord-segment-self)
        (inst '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n))))) snv)
        (bc `(IMPLIES (IN ,snv NN) (NOT (IN ,snv (ORD-SEGMENT ,snv)))))
        (ass)
    (refocus! use-cA-nk)
    (bc `(IMPLIES (IN ,skv (ORD-SEGMENT (succ ,snv)))
                  (NOT (IN ,snv (ORD-SEGMENT ,skv)))))
    (ass)
(refocus! use-cA-factGP)
(display "--- caseA: FACT-GP established ---\n") (show)

;;; ---- assemble:  reduce, splice, rearrange ----------------------------
(mac 'sum-ag-succ)               ; peel g(succ n) off LHS, gp(n) off RHS
(display "--- caseA: after mac sum-ag-succ ---\n") (show)
(subst cA-factIH)                ; SUM-AG(g,succ n) -> MUL(SUM-AG(gp,n), g(k))
(subst cA-factGP)                ; gp(n) -> g(succ n)
(display "--- caseA: after subst FACT-IH, FACT-GP ---\n") (show)
;;; abelian rearrangement:  (S*x)*y = (S*y)*x   via ag-mul-rearrange.
;;; (group-assoc cannot be used as a macete -- compound head -- so the
;;; reassociate+commute step is the installed lemma ag-mul-rearrange.)
(define cA-S `(SUM-AG ,sagv ,sgpv ,snv))
(define cA-x `(,sgv ,skv))
(define cA-y `(,sgv (succ ,snv)))
(define R-thm
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL a (IMPLIES (IN a (A ag))
       (FORALL b (IMPLIES (IN b (A ag))
         (FORALL c (IMPLIES (IN c (A ag))
           (= ((MUL ag) ((MUL ag) a b) c)
              ((MUL ag) ((MUL ag) a c) b)))))))))))
(define R-Fa
  `(FORALL a (IMPLIES (IN a (A ,sagv))
     (FORALL b (IMPLIES (IN b (A ,sagv))
       (FORALL c (IMPLIES (IN c (A ,sagv))
         (= ((MUL ,sagv) ((MUL ,sagv) a b) c)
            ((MUL ,sagv) ((MUL ,sagv) a c) b)))))))))
(define R-Fb
  `(FORALL b (IMPLIES (IN b (A ,sagv))
     (FORALL c (IMPLIES (IN c (A ,sagv))
       (= ((MUL ,sagv) ((MUL ,sagv) ,cA-S b) c)
          ((MUL ,sagv) ((MUL ,sagv) ,cA-S c) b)))))))
(define R-Fc
  `(FORALL c (IMPLIES (IN c (A ,sagv))
     (= ((MUL ,sagv) ((MUL ,sagv) ,cA-S ,cA-x) c)
        ((MUL ,sagv) ((MUL ,sagv) ,cA-S c) ,cA-x)))))
(define eqR
  `(= ((MUL ,sagv) ((MUL ,sagv) ,cA-S ,cA-x) ,cA-y)
      ((MUL ,sagv) ((MUL ,sagv) ,cA-S ,cA-y) ,cA-x)))
(ta 'ag-mul-rearrange)
(inst R-thm sagv)
(cut R-Fa)
(define u-cA-Ra (last-node))
  (bc `(IMPLIES (IS-ABELIAN-GROUP ,sagv) ,R-Fa)) (ass)
(refocus! u-cA-Ra)
(inst R-Fa cA-S)
(cut R-Fb)
(define u-cA-Rb (last-node))
  (bc `(IMPLIES (IN ,cA-S (A ,sagv)) ,R-Fb)) (ass)
(refocus! u-cA-Rb)
(inst R-Fb cA-x)
(cut R-Fc)
(define u-cA-Rc (last-node))
  (bc `(IMPLIES (IN ,cA-x (A ,sagv)) ,R-Fc)) (ass)
(refocus! u-cA-Rc)
(inst R-Fc cA-y)
(bc `(IMPLIES (IN ,cA-y (A ,sagv)) ,eqR))    ; goal eqR -> g(succ n) in A(ag)
(ass)
(display "--- caseA: DONE ---\n") (show)
    ))


;;; =====================================================================
;;; ARCHIVED: sum-ag-permutation-invariance  (originally proven-theorems.scm lines 1152-1821)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; sum-ag-permutation-invariance:  a finite abelian-group sum is invariant
;;; under any permutation of its index segment.  NN induction; step case
;;; uses sum-ag-splice-out + the IH with induced permutation
;;; INVERSE-BIJ(DELETE-AT inv K).  Dev file prover/scratch-perm-inv.scm.
;;; -----------------------------------------------------------------------
(prove-and-install! 'sum-ag-permutation-invariance
  (lambda ()
    (define pinv-goal
      '(FORALL n (IMPLIES (IN n NN)
         (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
         (FORALL g (IMPLIES (IN g (FUN NN (A ag)))
         (FORALL h (IMPLIES (IN h (FUN NN (A ag)))
         (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
         (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
           (= (SUM-AG ag g n) (SUM-AG ag h n))))))))))))))

    (sp (make-wff pinv-goal))
    (ni)

    ;;; ===== BASE CASE  n = 0 =====
    (di) (di) (di) (di)           ; peel ag,g,h,phi + assume IS-AG/funs/bij/agree
    (mac 'sum-ag-zero)            ; both sums -> E(ag)
    (rfl)

    ;;; ===== STEP CASE  n -> succ n =====
    (define sv *fresh-counter*)
    (define nv   (eigen-name 'n   sv))
    (define agv  (eigen-name 'ag  (+ sv 1)))
    (define gv   (eigen-name 'g   (+ sv 2)))
    (define hv   (eigen-name 'h   (+ sv 3)))
    (define phiv (eigen-name 'phi (+ sv 4)))
    (di) (di) (di) (di) (di) (di)   ; intro n, assume IH, peel ag/g/h/phi + asms

    ;;; term abbreviations
    (define osSn `(ORD-SEGMENT (succ ,nv)))
    (define osn  `(ORD-SEGMENT ,nv))
    (define K    `(,phiv ,nv))                       ; the spliced index
    (define inv  `(INVERSE-BIJ ,phiv ,osSn ,osSn))   ; phi inverse
    (define dgk  `(DELETE-AT ,gv ,K))                ; g with index K spliced out
    (define dik  `(DELETE-AT ,inv ,K))               ; induced permutation
    (define AGREE
      `(FORALL i (IMPLIES (IN i ,osSn) (= (,hv i) (,gv (,phiv i))))))

    ;;; fact 1:  succ n in NN
    (cut `(IN (succ ,nv) NN))
    (define u-snn (last-node))
      (ta 'nn-succ-closed)
      (inst '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))) nv)
      (bc `(IMPLIES (IN ,nv NN) (IN (succ ,nv) NN)))
      (ass)
    (refocus! u-snn)

    ;;; fact 2:  n in os(succ n)
    (cut `(IN ,nv ,osSn))
    (define u-ninSn (last-node))
      (mac 'ord-segment-nn-succ)        ; -> (OR (IN n os(n)) (= n n))
      (oi-r)
      (rfl)
    (refocus! u-ninSn)

    ;;; fact 3:  phi in FUN(os(succ n), os(succ n))
    (cut `(IN ,phiv (FUN ,osSn ,osSn)))
    (define u-phifun (last-node))
      (ta 'bijection-in-fun)
      (inst `(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))) osSn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn Y)) (IN phi (FUN ,osSn Y))))) osSn)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn ,osSn)) (IN phi (FUN ,osSn ,osSn))))
            phiv)
      (bc `(IMPLIES (IN ,phiv (BIJECTION ,osSn ,osSn)) (IN ,phiv (FUN ,osSn ,osSn))))
      (ass)
    (refocus! u-phifun)

    ;;; fact 4:  K = phi(n) in os(succ n)
    (cut `(IN ,K ,osSn))
    (define u-Kin (last-node))
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) phiv)
      (inst `(FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN ,phiv (FUN A B)) (IN x A)) (IN (,phiv x) B))))) osSn)
      (inst `(FORALL B (FORALL x
                (IMPLIES (AND (IN ,phiv (FUN ,osSn B)) (IN x ,osSn)) (IN (,phiv x) B))))
            osSn)
      (inst `(FORALL x (IMPLIES (AND (IN ,phiv (FUN ,osSn ,osSn)) (IN x ,osSn))
                                (IN (,phiv x) ,osSn))) nv)
      (bc `(IMPLIES (AND (IN ,phiv (FUN ,osSn ,osSn)) (IN ,nv ,osSn))
                    (IN ,K ,osSn)))
      (di)
      (define u-Kin2 (last-node))
        (ass)                           ; phi in FUN
      (refocus! u-Kin2)
        (ass)                           ; n in os(succ n)
    (refocus! u-Kin)

    ;;; fact 5:  inv in BIJECTION(os(succ n), os(succ n))
    (cut `(IN ,inv (BIJECTION ,osSn ,osSn)))
    (define u-invbij (last-node))
      (ta 'inverse-bij-is-bijection)
      (inst `(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y))
                         (IN (INVERSE-BIJ phi X Y) (BIJECTION Y X)))))) osSn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn Y))
                         (IN (INVERSE-BIJ phi ,osSn Y) (BIJECTION Y ,osSn))))) osSn)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn ,osSn))
                         (IN (INVERSE-BIJ phi ,osSn ,osSn) (BIJECTION ,osSn ,osSn))))
            phiv)
      (bc `(IMPLIES (IN ,phiv (BIJECTION ,osSn ,osSn))
                    (IN ,inv (BIJECTION ,osSn ,osSn))))
      (ass)
    (refocus! u-invbij)

    ;;; fact 6:  inv(K) = n   (inverse-bij-left: dom/cod-named)
    (cut `(= (,inv ,K) ,nv))
    (define u-invK (last-node))
      (ta 'inverse-bij-left)
      (inst '(FORALL dom (FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION dom cod))
                  (FORALL x (IMPLIES (IN x dom)
                    (= ((INVERSE-BIJ phi dom cod) (phi x)) x))))))) osSn)
      (inst `(FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn cod))
                  (FORALL x (IMPLIES (IN x ,osSn)
                    (= ((INVERSE-BIJ phi ,osSn cod) (phi x)) x)))))) osSn)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn ,osSn))
                  (FORALL x (IMPLIES (IN x ,osSn)
                    (= ((INVERSE-BIJ phi ,osSn ,osSn) (phi x)) x))))) phiv)
      (cut `(FORALL x (IMPLIES (IN x ,osSn) (= (,inv (,phiv x)) x))))
      (define u-invK2 (last-node))
        (bc `(IMPLIES (IN ,phiv (BIJECTION ,osSn ,osSn))
                (FORALL x (IMPLIES (IN x ,osSn) (= (,inv (,phiv x)) x)))))
        (ass)
      (refocus! u-invK2)
      (inst `(FORALL x (IMPLIES (IN x ,osSn) (= (,inv (,phiv x)) x))) nv)
      (bc `(IMPLIES (IN ,nv ,osSn) (= (,inv ,K) ,nv)))
      (ass)
    (refocus! u-invK)

    ;;; fact 7:  dik = DELETE-AT(inv,K) in BIJECTION(os n, os n)
    (cut `(IN ,dik (BIJECTION ,osn ,osn)))
    (define u-dikbij (last-node))
      (ta 'delete-at-is-bijection)
      (inst '(FORALL n (FORALL k (FORALL h
                (IMPLIES (AND (IN n NN)
                         (AND (IN k (ORD-SEGMENT (succ n)))
                         (AND (IN h (BIJECTION (ORD-SEGMENT (succ n))
                                               (ORD-SEGMENT (succ n))))
                              (= (h k) n))))
                         (IN (DELETE-AT h k)
                             (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n))))))) nv)
      (inst `(FORALL k (FORALL h
                (IMPLIES (AND (IN ,nv NN)
                         (AND (IN k ,osSn)
                         (AND (IN h (BIJECTION ,osSn ,osSn)) (= (h k) ,nv))))
                         (IN (DELETE-AT h k) (BIJECTION ,osn ,osn))))) K)
      (inst `(FORALL h
                (IMPLIES (AND (IN ,nv NN)
                         (AND (IN ,K ,osSn)
                         (AND (IN h (BIJECTION ,osSn ,osSn)) (= (h ,K) ,nv))))
                         (IN (DELETE-AT h ,K) (BIJECTION ,osn ,osn)))) inv)
      (bc `(IMPLIES (AND (IN ,nv NN)
                    (AND (IN ,K ,osSn)
                    (AND (IN ,inv (BIJECTION ,osSn ,osSn)) (= (,inv ,K) ,nv))))
                    (IN ,dik (BIJECTION ,osn ,osn))))
      (di)                              ; split AND -> [n in NN] [AND ...]
      (define u-dik-a2 (last-node))
        (ass)                           ; n in NN
      (refocus! u-dik-a2)
      (di)                              ; split -> [K in osSn] [AND ...]
      (define u-dik-a3 (last-node))
        (ass)                           ; K in os(succ n)
      (refocus! u-dik-a3)
      (di)                              ; split -> [inv in BIJ] [inv(K)=n]
      (define u-dik-a4 (last-node))
        (ass)                           ; inv in BIJECTION
      (refocus! u-dik-a4)
        (ass)                           ; inv(K) = n
    (refocus! u-dikbij)

    ;;; fact 8:  dgk = DELETE-AT(g,K) in FUN(NN, A(ag))
    (cut `(IN ,dgk (FUN NN (A ,agv))))
    (define u-dgkfun (last-node))
      (ta 'delete-at-in-fun)
      (inst '(FORALL B (FORALL h (FORALL k
                (IMPLIES (IN h (FUN NN B)) (IN (DELETE-AT h k) (FUN NN B))))))
            `(A ,agv))
      (inst `(FORALL h (FORALL k
                (IMPLIES (IN h (FUN NN (A ,agv)))
                         (IN (DELETE-AT h k) (FUN NN (A ,agv)))))) gv)
      (inst `(FORALL k (IMPLIES (IN ,gv (FUN NN (A ,agv)))
                                (IN (DELETE-AT ,gv k) (FUN NN (A ,agv))))) K)
      (bc `(IMPLIES (IN ,gv (FUN NN (A ,agv))) (IN ,dgk (FUN NN (A ,agv)))))
      (ass)
    (refocus! u-dgkfun)

    ;;; fact 9:  h(n) = g(K)
    (cut `(= (,hv ,nv) (,gv ,K)))
    (define u-hn (last-node))
      (inst AGREE nv)
      (bc `(IMPLIES (IN ,nv ,osSn) (= (,hv ,nv) (,gv (,phiv ,nv)))))
      (ass)
    (refocus! u-hn)

    ;;; FACT-H:  SUM-AG(h,succ n) = MUL(SUM-AG(h,n), h(n))
    (cut `(= (SUM-AG ,agv ,hv (succ ,nv))
             ((MUL ,agv) (SUM-AG ,agv ,hv ,nv) (,hv ,nv))))
    (define u-factH (last-node))
      (ta 'sum-ag-succ)
      (inst '(FORALL ag (FORALL f (FORALL n (IMPLIES (IN n NN)
                (= (SUM-AG ag f (succ n))
                   ((MUL ag) (SUM-AG ag f n) (f n))))))) agv)
      (inst `(FORALL f (FORALL n (IMPLIES (IN n NN)
                (= (SUM-AG ,agv f (succ n))
                   ((MUL ,agv) (SUM-AG ,agv f n) (f n)))))) hv)
      (inst `(FORALL n (IMPLIES (IN n NN)
                (= (SUM-AG ,agv ,hv (succ n))
                   ((MUL ,agv) (SUM-AG ,agv ,hv n) (,hv n))))) nv)
      (bc `(IMPLIES (IN ,nv NN)
              (= (SUM-AG ,agv ,hv (succ ,nv))
                 ((MUL ,agv) (SUM-AG ,agv ,hv ,nv) (,hv ,nv)))))
      (ass)
    (refocus! u-factH)

    ;;; capture-free substitution, for building instantiation intermediates
    (define (S v t f) (subst-free v t f))

    ;;; fact 4b:  K in NN
    (cut `(IN ,K NN))
    (define u-Knn (last-node))
      (ta 'ord-segment-nn-subset)
      (inst '(FORALL m (IMPLIES (IN m NN)
                (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN)))))
            `(succ ,nv))
      (cut `(FORALL k (IMPLIES (IN k ,osSn) (IN k NN))))
      (define u-Knn2 (last-node))
        (bc `(IMPLIES (IN (succ ,nv) NN)
                (FORALL k (IMPLIES (IN k ,osSn) (IN k NN)))))
        (ass)
      (refocus! u-Knn2)
      (inst `(FORALL k (IMPLIES (IN k ,osSn) (IN k NN))) K)
      (bc `(IMPLIES (IN ,K ,osSn) (IN ,K NN)))
      (ass)
    (refocus! u-Knn)

    ;;; ===== FACT-G:  SUM-AG(g,succ n) = MUL(SUM-AG(DELETE-AT g K,n), g(K)) =====
    (define spliceout
      '(FORALL n (IMPLIES (IN n NN)
         (FORALL ag (FORALL g (FORALL k (FORALL gp
           (IMPLIES (IS-ABELIAN-GROUP ag)
           (IMPLIES (IN g (FUN NN (A ag)))
           (IMPLIES (IN gp (FUN NN (A ag)))
           (IMPLIES (IN k (ORD-SEGMENT (succ n)))
           (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k)) (= (gp i) (g i))))
           (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT n))
                                            (NOT (IN i (ORD-SEGMENT k))))
                                       (= (gp i) (g (succ i)))))
             (= (SUM-AG ag g (succ n))
                ((MUL ag) (SUM-AG ag gp n) (g k))))))))))))))))
    (define G-tmpl     ; splice-out's inner 6-implication, n/ag/g/k/gp generic
      '(IMPLIES (IS-ABELIAN-GROUP ag)
       (IMPLIES (IN g (FUN NN (A ag)))
       (IMPLIES (IN gp (FUN NN (A ag)))
       (IMPLIES (IN k (ORD-SEGMENT (succ n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT k)) (= (gp i) (g i))))
       (IMPLIES (FORALL i (IMPLIES (AND (IN i (ORD-SEGMENT n))
                                        (NOT (IN i (ORD-SEGMENT k))))
                                   (= (gp i) (g (succ i)))))
         (= (SUM-AG ag g (succ n)) ((MUL ag) (SUM-AG ag gp n) (g k))))))))))
    (define G5 (S 'n nv G-tmpl))
    (define BODY-nv `(FORALL ag (FORALL g (FORALL k (FORALL gp ,G5)))))
    (define G4 (S 'ag agv G5))
    (define BODY-ag `(FORALL g (FORALL k (FORALL gp ,G4))))
    (define G3 (S 'g gv G4))
    (define BODY-g `(FORALL k (FORALL gp ,G3)))
    (define G2 (S 'k K G3))
    (define BODY-k `(FORALL gp ,G2))
    (define impl6 (S 'gp dgk G2))
    (define GT2 (caddr impl6))
    (define GT3 (caddr GT2))
    (define GT4 (caddr GT3))
    (define GT5 (caddr GT4))
    (define GT6 (caddr GT5))
    (define G-AGREE2 (cadr GT6))
    (define FACT-G (caddr GT6))

    (cut FACT-G)
    (define u-factG (last-node))
      ;; AGREE1:  delete-at-below-k at h:=g, k:=K
      (ta 'delete-at-below-k)
      (inst '(FORALL h (FORALL k (FORALL i
                (IMPLIES (IN i (ORD-SEGMENT k)) (= ((DELETE-AT h k) i) (h i))))))
            gv)
      (inst `(FORALL k (FORALL i
                (IMPLIES (IN i (ORD-SEGMENT k))
                         (= ((DELETE-AT ,gv k) i) (,gv i))))) K)
      ;; AGREE2:  sub-proof from delete-at-above-k
      (cut G-AGREE2)
      (define u-spag (last-node))
        (define ci2 *fresh-counter*)
        (define iv2 (eigen-name 'i ci2))
        (di) (di)                  ; intro i, assume (AND i in os(n), i notin os(K))
        (ai `(AND (IN ,iv2 (ORD-SEGMENT ,nv)) (NOT (IN ,iv2 (ORD-SEGMENT ,K)))))
        (cut `(IN ,iv2 NN))
        (define u-iNN (last-node))
          (ta 'ord-segment-nn-subset)
          (inst '(FORALL m (IMPLIES (IN m NN)
                    (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN))))) nv)
          (cut `(FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN))))
          (define u-iNN2 (last-node))
            (bc `(IMPLIES (IN ,nv NN)
                    (FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN)))))
            (ass)
          (refocus! u-iNN2)
          (inst `(FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN))) iv2)
          (bc `(IMPLIES (IN ,iv2 (ORD-SEGMENT ,nv)) (IN ,iv2 NN)))
          (ass)
        (refocus! u-iNN)
        (ta 'delete-at-above-k)
        (inst '(FORALL h (FORALL k (FORALL i
                  (IMPLIES (AND (IN i NN)
                           (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                           (= ((DELETE-AT h k) i) (h (succ i))))))) gv)
        (inst `(FORALL k (FORALL i
                  (IMPLIES (AND (IN i NN)
                           (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                           (= ((DELETE-AT ,gv k) i) (,gv (succ i)))))) K)
        (inst `(FORALL i
                  (IMPLIES (AND (IN i NN)
                           (AND (IN ,K NN) (NOT (IN i (ORD-SEGMENT ,K)))))
                           (= ((DELETE-AT ,gv ,K) i) (,gv (succ i))))) iv2)
        (bc `(IMPLIES (AND (IN ,iv2 NN)
                      (AND (IN ,K NN) (NOT (IN ,iv2 (ORD-SEGMENT ,K)))))
                      (= (,dgk ,iv2) (,gv (succ ,iv2)))))
        (di)                       ; split AND -> [i in NN] [AND ...]
        (define u-spagb (last-node))
          (ass)
        (refocus! u-spagb)
        (di)                       ; -> [K in NN] [i notin os(K)]
        (define u-spagc (last-node))
          (ass)
        (refocus! u-spagc)
          (ass)
      (refocus! u-spag)
      ;; instantiate splice-out
      (ta 'sum-ag-splice-out)
      (inst spliceout nv)
      (cut BODY-nv)
      (define u-Gbnv (last-node))
        (bc `(IMPLIES (IN ,nv NN) ,BODY-nv))
        (ass)
      (refocus! u-Gbnv)
      (inst BODY-nv agv)
      (inst BODY-ag gv)
      (inst BODY-g  K)
      (inst BODY-k  dgk)
      (cut GT2) (define uG2 (last-node)) (bc impl6) (ass) (refocus! uG2)
      (cut GT3) (define uG3 (last-node)) (bc GT2)   (ass) (refocus! uG3)
      (cut GT4) (define uG4 (last-node)) (bc GT3)   (ass) (refocus! uG4)
      (cut GT5) (define uG5 (last-node)) (bc GT4)   (ass) (refocus! uG5)
      (cut GT6) (define uG6 (last-node)) (bc GT5)   (ass) (refocus! uG6)
      (bc GT6) (ass)
    (refocus! u-factG)

    ;;; ===== FACT-IND:  SUM-AG(h,n) = SUM-AG(DELETE-AT g K, n)  via the IH =====
    (define INNER-tmpl
      '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
         (FORALL g (IMPLIES (IN g (FUN NN (A ag)))
         (FORALL h (IMPLIES (IN h (FUN NN (A ag)))
         (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
         (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
           (= (SUM-AG ag g n) (SUM-AG ag h n))))))))))))
    (define IH       (S 'n nv INNER-tmpl))
    (define I1       (S 'ag agv (caddr IH)))
    (define IH-Fg    (caddr I1))
    (define I2       (S 'g hv (caddr IH-Fg)))
    (define IH-Fh    (caddr I2))
    (define I3       (S 'h dgk (caddr IH-Fh)))
    (define IH-Fphi  (caddr I3))
    (define I4       (S 'phi dik (caddr IH-Fphi)))
    (define IH-P5C   (caddr I4))
    (define AGREE-prime (cadr IH-P5C))
    (define FACT-IND (caddr IH-P5C))

    ;;; shared facts for AGREE-prime:  inv typing and the inverse-bij-right form
    (cut `(IN ,inv (FUN ,osSn ,osSn)))
    (define u-invfun (last-node))
      (ta 'bijection-in-fun)
      (inst `(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))) osSn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn Y)) (IN phi (FUN ,osSn Y))))) osSn)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn ,osSn)) (IN phi (FUN ,osSn ,osSn))))
            inv)
      (bc `(IMPLIES (IN ,inv (BIJECTION ,osSn ,osSn)) (IN ,inv (FUN ,osSn ,osSn))))
      (ass)
    (refocus! u-invfun)

    (define invright `(FORALL y (IMPLIES (IN y ,osSn) (= (,phiv (,inv y)) y))))
    (cut invright)
    (define u-invr (last-node))
      (ta 'inverse-bij-right)
      (inst '(FORALL dom (FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION dom cod))
                  (FORALL y (IMPLIES (IN y cod)
                    (= (phi ((INVERSE-BIJ phi dom cod) y)) y))))))) osSn)
      (inst `(FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn cod))
                  (FORALL y (IMPLIES (IN y cod)
                    (= (phi ((INVERSE-BIJ phi ,osSn cod) y)) y)))))) osSn)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osSn ,osSn))
                  (FORALL y (IMPLIES (IN y ,osSn)
                    (= (phi ((INVERSE-BIJ phi ,osSn ,osSn) y)) y))))) phiv)
      (bc `(IMPLIES (IN ,phiv (BIJECTION ,osSn ,osSn)) ,invright))
      (ass)
    (refocus! u-invr)

    (cut FACT-IND)
    (define u-factIND (last-node))
      (inst IH agv)
      (cut IH-Fg)   (define uI1 (last-node)) (bc I1) (ass) (refocus! uI1)
      (inst IH-Fg hv)
      (cut IH-Fh)   (define uI2 (last-node)) (bc I2) (ass) (refocus! uI2)
      (inst IH-Fh dgk)
      (cut IH-Fphi) (define uI3 (last-node)) (bc I3) (ass) (refocus! uI3)
      (inst IH-Fphi dik)
      (cut IH-P5C)  (define uI4 (last-node)) (bc I4) (ass) (refocus! uI4)
      (bc IH-P5C)                 ; goal FACT-IND -> AGREE-prime
      ;; ----- prove AGREE-prime:  forall i in os(n). dgk(i) = h(dik(i)) -----
      (define ci3 *fresh-counter*)
      (define iv3 (eigen-name 'i ci3))
      (di)                        ; intro i, assume i in os(n)
      ;; shared per-i facts
      (cut `(IN ,iv3 ,osSn))
      (define u-i3Sn (last-node))
        (mac 'ord-segment-nn-succ) (oi-l) (ass)
      (refocus! u-i3Sn)
      (cut `(IN ,iv3 NN))
      (define u-i3NN (last-node))
        (ta 'ord-segment-nn-subset)
        (inst '(FORALL m (IMPLIES (IN m NN)
                  (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN))))) nv)
        (cut `(FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN))))
        (define u-i3NN2 (last-node))
          (bc `(IMPLIES (IN ,nv NN)
                  (FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN)))))
          (ass)
        (refocus! u-i3NN2)
        (inst `(FORALL k (IMPLIES (IN k (ORD-SEGMENT ,nv)) (IN k NN))) iv3)
        (bc `(IMPLIES (IN ,iv3 (ORD-SEGMENT ,nv)) (IN ,iv3 NN)))
        (ass)
      (refocus! u-i3NN)
      ;; excluded middle on  P := i in os(K)
      (cut `(OR (IN ,iv3 (ORD-SEGMENT ,K)) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
      (define u-em (last-node))
        (pbc)                     ; assume H = NOT(OR P (NOT P)), goal FALSITY
        (cut `(NOT (IN ,iv3 (ORD-SEGMENT ,K))))
        (define u-em2 (last-node))
          (di)                    ; assume P, goal FALSITY
          (cut `(OR (IN ,iv3 (ORD-SEGMENT ,K)) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
          (define u-em3 (last-node))
            (oi-l) (ass)
          (refocus! u-em3)
          (ai `(NOT (OR (IN ,iv3 (ORD-SEGMENT ,K))
                        (NOT (IN ,iv3 (ORD-SEGMENT ,K))))))
        (refocus! u-em2)
        (cut `(OR (IN ,iv3 (ORD-SEGMENT ,K)) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
        (define u-em4 (last-node))
          (oi-r) (ass)
        (refocus! u-em4)
        (ai `(NOT (OR (IN ,iv3 (ORD-SEGMENT ,K))
                      (NOT (IN ,iv3 (ORD-SEGMENT ,K))))))
      (refocus! u-em)
      (ai `(OR (IN ,iv3 (ORD-SEGMENT ,K)) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
      (define caseNP (last-node))
        ;; ===== case P:  i in os(K) =====
        ;; db:  dgk(i) = g(i)
        (cut `(= (,dgk ,iv3) (,gv ,iv3)))
        (define u-db (last-node))
          (ta 'delete-at-below-k)
          (inst '(FORALL h (FORALL k (FORALL i
                    (IMPLIES (IN i (ORD-SEGMENT k))
                             (= ((DELETE-AT h k) i) (h i)))))) gv)
          (inst `(FORALL k (FORALL i
                    (IMPLIES (IN i (ORD-SEGMENT k))
                             (= ((DELETE-AT ,gv k) i) (,gv i))))) K)
          (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,K))
                             (= (,dgk i) (,gv i)))) iv3)
          (bc `(IMPLIES (IN ,iv3 (ORD-SEGMENT ,K)) (= (,dgk ,iv3) (,gv ,iv3))))
          (ass)
        (refocus! u-db)
        ;; di:  dik(i) = inv(i)
        (cut `(= (,dik ,iv3) (,inv ,iv3)))
        (define u-di (last-node))
          (ta 'delete-at-below-k)
          (inst '(FORALL h (FORALL k (FORALL i
                    (IMPLIES (IN i (ORD-SEGMENT k))
                             (= ((DELETE-AT h k) i) (h i)))))) inv)
          (inst `(FORALL k (FORALL i
                    (IMPLIES (IN i (ORD-SEGMENT k))
                             (= ((DELETE-AT ,inv k) i) (,inv i))))) K)
          (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,K))
                             (= (,dik i) (,inv i)))) iv3)
          (bc `(IMPLIES (IN ,iv3 (ORD-SEGMENT ,K)) (= (,dik ,iv3) (,inv ,iv3))))
          (ass)
        (refocus! u-di)
        ;; inv(i) in os(succ n)
        (cut `(IN (,inv ,iv3) ,osSn))
        (define u-invi (last-node))
          (ta 'fun-apply-type)
          (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                    (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) inv)
          (inst `(FORALL A (FORALL B (FORALL x
                    (IMPLIES (AND (IN ,inv (FUN A B)) (IN x A))
                             (IN (,inv x) B))))) osSn)
          (inst `(FORALL B (FORALL x
                    (IMPLIES (AND (IN ,inv (FUN ,osSn B)) (IN x ,osSn))
                             (IN (,inv x) B)))) osSn)
          (inst `(FORALL x (IMPLIES (AND (IN ,inv (FUN ,osSn ,osSn)) (IN x ,osSn))
                                    (IN (,inv x) ,osSn))) iv3)
          (bc `(IMPLIES (AND (IN ,inv (FUN ,osSn ,osSn)) (IN ,iv3 ,osSn))
                        (IN (,inv ,iv3) ,osSn)))
          (di) (define u-invi2 (last-node)) (ass) (refocus! u-invi2) (ass)
        (refocus! u-invi)
        ;; pr1:  phi(inv(i)) = i
        (cut `(= (,phiv (,inv ,iv3)) ,iv3))
        (define u-pr1 (last-node))
          (inst invright iv3)
          (bc `(IMPLIES (IN ,iv3 ,osSn) (= (,phiv (,inv ,iv3)) ,iv3)))
          (ass)
        (refocus! u-pr1)
        ;; ag1:  h(inv(i)) = g(phi(inv(i)))
        (cut `(= (,hv (,inv ,iv3)) (,gv (,phiv (,inv ,iv3)))))
        (define u-ag1 (last-node))
          (inst AGREE `(,inv ,iv3))
          (bc `(IMPLIES (IN (,inv ,iv3) ,osSn)
                        (= (,hv (,inv ,iv3)) (,gv (,phiv (,inv ,iv3))))))
          (ass)
        (refocus! u-ag1)
        ;; combine
        (subst `(= (,dgk ,iv3) (,gv ,iv3)))
        (subst `(= (,dik ,iv3) (,inv ,iv3)))
        (subst `(= (,hv (,inv ,iv3)) (,gv (,phiv (,inv ,iv3)))))
        (subst `(= (,phiv (,inv ,iv3)) ,iv3))
        (rfl)
      (refocus! caseNP)
        ;; ===== case NOT P:  i notin os(K) =====
        ;; db2:  dgk(i) = g(succ i)
        (cut `(= (,dgk ,iv3) (,gv (succ ,iv3))))
        (define u-db2 (last-node))
          (ta 'delete-at-above-k)
          (inst '(FORALL h (FORALL k (FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                             (= ((DELETE-AT h k) i) (h (succ i))))))) gv)
          (inst `(FORALL k (FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                             (= ((DELETE-AT ,gv k) i) (,gv (succ i)))))) K)
          (inst `(FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN ,K NN) (NOT (IN i (ORD-SEGMENT ,K)))))
                             (= ((DELETE-AT ,gv ,K) i) (,gv (succ i))))) iv3)
          (bc `(IMPLIES (AND (IN ,iv3 NN)
                        (AND (IN ,K NN) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
                        (= (,dgk ,iv3) (,gv (succ ,iv3)))))
          (di) (define u-db2b (last-node)) (ass) (refocus! u-db2b)
          (di) (define u-db2c (last-node)) (ass) (refocus! u-db2c) (ass)
        (refocus! u-db2)
        ;; di2:  dik(i) = inv(succ i)
        (cut `(= (,dik ,iv3) (,inv (succ ,iv3))))
        (define u-di2 (last-node))
          (ta 'delete-at-above-k)
          (inst '(FORALL h (FORALL k (FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                             (= ((DELETE-AT h k) i) (h (succ i))))))) inv)
          (inst `(FORALL k (FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
                             (= ((DELETE-AT ,inv k) i) (,inv (succ i)))))) K)
          (inst `(FORALL i
                    (IMPLIES (AND (IN i NN)
                             (AND (IN ,K NN) (NOT (IN i (ORD-SEGMENT ,K)))))
                             (= ((DELETE-AT ,inv ,K) i) (,inv (succ i))))) iv3)
          (bc `(IMPLIES (AND (IN ,iv3 NN)
                        (AND (IN ,K NN) (NOT (IN ,iv3 (ORD-SEGMENT ,K)))))
                        (= (,dik ,iv3) (,inv (succ ,iv3)))))
          (di) (define u-di2b (last-node)) (ass) (refocus! u-di2b)
          (di) (define u-di2c (last-node)) (ass) (refocus! u-di2c) (ass)
        (refocus! u-di2)
        ;; succ i in os(succ n)
        (cut `(IN (succ ,iv3) ,osSn))
        (define u-si (last-node))
          (ta 'ord-segment-succ-monotone)
          (inst '(FORALL n (IMPLIES (IN n NN)
                    (FORALL i (IMPLIES (IN i (ORD-SEGMENT n))
                      (IN (succ i) (ORD-SEGMENT (succ n))))))) nv)
          (cut `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv))
                    (IN (succ i) ,osSn))))
          (define u-si2 (last-node))
            (bc `(IMPLIES (IN ,nv NN)
                    (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv))
                      (IN (succ i) ,osSn)))))
            (ass)
          (refocus! u-si2)
          (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv))
                    (IN (succ i) ,osSn))) iv3)
          (bc `(IMPLIES (IN ,iv3 (ORD-SEGMENT ,nv)) (IN (succ ,iv3) ,osSn)))
          (ass)
        (refocus! u-si)
        ;; inv(succ i) in os(succ n)
        (cut `(IN (,inv (succ ,iv3)) ,osSn))
        (define u-invsi (last-node))
          (ta 'fun-apply-type)
          (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                    (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) inv)
          (inst `(FORALL A (FORALL B (FORALL x
                    (IMPLIES (AND (IN ,inv (FUN A B)) (IN x A))
                             (IN (,inv x) B))))) osSn)
          (inst `(FORALL B (FORALL x
                    (IMPLIES (AND (IN ,inv (FUN ,osSn B)) (IN x ,osSn))
                             (IN (,inv x) B)))) osSn)
          (inst `(FORALL x (IMPLIES (AND (IN ,inv (FUN ,osSn ,osSn)) (IN x ,osSn))
                                    (IN (,inv x) ,osSn))) `(succ ,iv3))
          (bc `(IMPLIES (AND (IN ,inv (FUN ,osSn ,osSn)) (IN (succ ,iv3) ,osSn))
                        (IN (,inv (succ ,iv3)) ,osSn)))
          (di) (define u-invsi2 (last-node)) (ass) (refocus! u-invsi2) (ass)
        (refocus! u-invsi)
        ;; pr2:  phi(inv(succ i)) = succ i
        (cut `(= (,phiv (,inv (succ ,iv3))) (succ ,iv3)))
        (define u-pr2 (last-node))
          (inst invright `(succ ,iv3))
          (bc `(IMPLIES (IN (succ ,iv3) ,osSn)
                        (= (,phiv (,inv (succ ,iv3))) (succ ,iv3))))
          (ass)
        (refocus! u-pr2)
        ;; ag2:  h(inv(succ i)) = g(phi(inv(succ i)))
        (cut `(= (,hv (,inv (succ ,iv3))) (,gv (,phiv (,inv (succ ,iv3))))))
        (define u-ag2 (last-node))
          (inst AGREE `(,inv (succ ,iv3)))
          (bc `(IMPLIES (IN (,inv (succ ,iv3)) ,osSn)
                        (= (,hv (,inv (succ ,iv3)))
                           (,gv (,phiv (,inv (succ ,iv3)))))))
          (ass)
        (refocus! u-ag2)
        ;; combine
        (subst `(= (,dgk ,iv3) (,gv (succ ,iv3))))
        (subst `(= (,dik ,iv3) (,inv (succ ,iv3))))
        (subst `(= (,hv (,inv (succ ,iv3))) (,gv (,phiv (,inv (succ ,iv3))))))
        (subst `(= (,phiv (,inv (succ ,iv3))) (succ ,iv3)))
        (rfl)
    (refocus! u-factIND)

    ;;; ===== assemble =====
    (subst FACT-G)
    (subst `(= (SUM-AG ,agv ,hv (succ ,nv))
               ((MUL ,agv) (SUM-AG ,agv ,hv ,nv) (,hv ,nv))))
    (subst `(= (,hv ,nv) (,gv ,K)))
    (subst FACT-IND)
    (rfl)
))


;;; =====================================================================
;;; ARCHIVED: finsum-congruence  (originally proven-theorems.scm lines 2742-2928)
;;; =====================================================================

;;; -----------------------------------------------------------------------
;;; finsum-congruence:  f and g agreeing on S forces FINSUM(ag,f,S) =
;;; FINSUM(ag,g,S).  mac FINSUM exposes both SUM-AGs over the same
;;; enumeration FIN-ENUM(S); sum-ag-congruence reduces to agreement of the
;;; two ENUM-FAM families on ORD-SEGMENT(CARD S), which holds because
;;; FIN-ENUM(S)(i) in S and f, g agree there.
;;; Developed in prover/scratch-fs2.scm.
(prove-and-install! 'finsum-congruence
  (lambda ()
    (define (S v t f) (subst-free v t f))
    (sp (make-wff
         '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
            (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
            (FORALL f (IMPLIES (IN f (FUN S (A ag)))
            (FORALL g (IMPLIES (IN g (FUN S (A ag)))
            (IMPLIES (FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
              (= (FINSUM ag f S) (FINSUM ag g S))))))))))))))
    (define c0 *fresh-counter*)
    (define agv (eigen-name 'ag c0))
    (define Sv  (eigen-name 'S  (+ c0 1)))
    (define fv  (eigen-name 'f  (+ c0 2)))
    (define gv  (eigen-name 'g  (+ c0 3)))
    (di)(di)(di)(di)(di)(di)(di)

    (define osn   `(ORD-SEGMENT (CARD ,Sv)))
    (define feS   `(FIN-ENUM ,Sv))
    (define ncard `(CARD ,Sv))
    (define EFf `(ENUM-FAM ,agv ,fv ,feS ,ncard))
    (define EFg `(ENUM-FAM ,agv ,gv ,feS ,ncard))

    ;; enum-fam-in-fun chain (shared prefix; f-slot varies)
    (define EF '(FORALL n (IMPLIES (IN n NN)
       (FORALL ag (IMPLIES (IS-GROUP ag)
       (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
       (FORALL f (IMPLIES (IN f (FUN S (A ag)))
         (IN (ENUM-FAM ag f phi n) (FUN NN (A ag)))))))))))))
    (define EFn  (S 'n ncard (caddr EF)))
    (define EX1  (caddr EFn))
    (define EFag (S 'ag agv (caddr EX1)))
    (define EX2  (caddr EFag))
    (define EFS  (S 'S Sv (caddr EX2)))
    (define EFphi (S 'phi feS (caddr EFS)))
    (define EX3   (caddr EFphi))

    ;; sum-ag-congruence chain
    (define SC '(FORALL m (IMPLIES (IN m NN)
       (FORALL ag (FORALL g (FORALL gp
       (IMPLIES (IS-ABELIAN-GROUP ag)
       (IMPLIES (IN g (FUN NN (A ag)))
       (IMPLIES (IN gp (FUN NN (A ag)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT m)) (= (g i) (gp i))))
                (= (SUM-AG ag g m) (SUM-AG ag gp m))))))))))))
    (define SCm  (S 'm ncard (caddr SC)))
    (define SCX1 (caddr SCm))
    (define SCag (S 'ag agv (caddr SCX1)))
    (define SCg  (S 'g EFf (caddr SCag)))
    (define SCgp (S 'gp EFg (caddr SCg)))
    (define SCT2 (caddr SCgp))
    (define SCT3 (caddr SCT2))
    (define SCT4 (caddr SCT3))

    ;; helpers
    (define (feb-inline)
      (ta 'fin-enum-is-bijection)
      (inst '(FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
                (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S))))) Sv)
      (cut `(IMPLIES (IN (CARD ,Sv) NN)
               (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))))
      (let ((u (last-node)))
        (bc `(IMPLIES (IN ,Sv SET)
                (IMPLIES (IN (CARD ,Sv) NN)
                   (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv)))))
        (ass)
        (refocus! u)
        (bc `(IMPLIES (IN (CARD ,Sv) NN)
                (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))))
        (ass)))
    (define (isg-inline)
      (ta 'abelian-group-is-group)
      (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) agv)
      (bc `(IMPLIES (IS-ABELIAN-GROUP ,agv) (IS-GROUP ,agv)))
      (ass))
    (define (bij-in-fun-inline pt)
      (ta 'bijection-in-fun)
      (inst '(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))) osn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn Y)) (IN phi (FUN ,osn Y))))) Sv)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn ,Sv)) (IN phi (FUN ,osn ,Sv)))) pt)
      (bc `(IMPLIES (IN ,pt (BIJECTION ,osn ,Sv)) (IN ,pt (FUN ,osn ,Sv)))))
    ;; proves goal (IN (ENUM-FAM agv fterm feS ncard) (FUN NN (A agv)))
    (define (ef-in-fun-proof fterm)
      (let ((EFf2 (S 'f fterm (caddr EX3))))
        (ta 'enum-fam-in-fun)
        (inst EF ncard)
        (cut EX1) (let ((u (last-node))) (bc EFn) (ass) (refocus! u))
        (inst EX1 agv)
        (cut EX2) (let ((u (last-node))) (bc EFag) (isg-inline) (refocus! u))
        (inst EX2 Sv)
        (inst EFS feS)
        (cut EX3) (let ((u (last-node)))
                    (bc EFphi) (bij-in-fun-inline feS) (feb-inline) (refocus! u))
        (inst EX3 fterm)
        (bc (S 'f fterm (caddr EX3)))
        (ass)))

    ;; ---- proof ----
    ;; FACT-feSfun: (IN feS (FUN osn Sv))
    (cut `(IN ,feS (FUN ,osn ,Sv)))
    (define u-ff (last-node))
      (bij-in-fun-inline feS)
      (feb-inline)
    (refocus! u-ff)
    ;; FACT-ef-f
    (cut `(IN ,EFf (FUN NN (A ,agv))))
    (define u-eff (last-node))
      (ef-in-fun-proof fv)
    (refocus! u-eff)
    ;; FACT-ef-g
    (cut `(IN ,EFg (FUN NN (A ,agv))))
    (define u-efg (last-node))
      (ef-in-fun-proof gv)
    (refocus! u-efg)

    (mac 'FINSUM)
    ;; goal: (= (SUM-AG agv EFf ncard) (SUM-AG agv EFg ncard))

    (ta 'sum-ag-congruence)
    (inst SC ncard)
    (cut SCX1) (define uX1 (last-node)) (bc SCm) (ass) (refocus! uX1)
    (inst SCX1 agv)
    (inst SCag EFf)
    (inst SCg EFg)
    (cut SCT2) (define uT2 (last-node)) (bc SCgp) (ass) (refocus! uT2)
    (cut SCT3) (define uT3 (last-node)) (bc SCT2) (ass) (refocus! uT3)
    (cut SCT4) (define uT4 (last-node)) (bc SCT3) (ass) (refocus! uT4)
    (bc SCT4)
    ;; goal: AGREE' = (FORALL i (IMPLIES (IN i osn) (= (EFf i) (EFg i))))
    (define ic *fresh-counter*)
    (define iv (eigen-name 'i ic))
    (di)
    ;; goal: (= (EFf iv) (EFg iv))
    (mac 'ENUM-FAM)
    (lam-b)
    ;; goal: (= (IF (IN iv osn) (fv (feS iv)) (E agv)) (IF (IN iv osn) (gv (feS iv)) (E agv)))
    (if-true `(IF (IN ,iv ,osn) (,fv (,feS ,iv)) (E ,agv)))
    (define u-lt (last-node))
      (ass)
    (refocus! u-lt)
    (subst `(= (IF (IN ,iv ,osn) (,fv (,feS ,iv)) (E ,agv)) (,fv (,feS ,iv))))
    (if-true `(IF (IN ,iv ,osn) (,gv (,feS ,iv)) (E ,agv)))
    (define u-rt (last-node))
      (ass)
    (refocus! u-rt)
    (subst `(= (IF (IN ,iv ,osn) (,gv (,feS ,iv)) (E ,agv)) (,gv (,feS ,iv))))
    ;; goal: (= (fv (feS iv)) (gv (feS iv)))
    ;; FACT-fsi: (IN (feS iv) Sv)
    (cut `(IN (,feS ,iv) ,Sv))
    (define u-fsi (last-node))
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) feS)
      (inst `(FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN ,feS (FUN A B)) (IN x A)) (IN (,feS x) B)))))
            osn)
      (inst `(FORALL B (FORALL x
                (IMPLIES (AND (IN ,feS (FUN ,osn B)) (IN x ,osn)) (IN (,feS x) B))))
            Sv)
      (inst `(FORALL x (IMPLIES (AND (IN ,feS (FUN ,osn ,Sv)) (IN x ,osn))
                                (IN (,feS x) ,Sv))) iv)
      (bc `(IMPLIES (AND (IN ,feS (FUN ,osn ,Sv)) (IN ,iv ,osn))
                    (IN (,feS ,iv) ,Sv)))
      (di)
      (define u-fsia (last-node))
        (ass)
      (refocus! u-fsia)
        (ass)
    (refocus! u-fsi)
    ;; use congruence hypothesis at z := (feS iv)
    (inst `(FORALL z (IMPLIES (IN z ,Sv) (= (,fv z) (,gv z)))) `(,feS ,iv))
    (bc `(IMPLIES (IN (,feS ,iv) ,Sv) (= (,fv (,feS ,iv)) (,gv (,feS ,iv)))))
    (ass)))



(display ";; proven-theorems.scm: all library proofs verified.\n")


;;; =====================================================================
;;; 2026-05-27 PSS PROMOTION BATCH (14 entries)
;;;
;;; The proven theorems below were promoted to PSS entries in
;;; theorem-library/.  Each statement was lifted into a (support ...)
;;; entry; the proof scripts (with their original doc comments) are
;;; preserved here for audit.  After this batch, proven-theorems.scm is
;;; empty and has been removed from load.scm.
;;; =====================================================================

;;; ---------------------------------------------------------------------
;;; ARCHIVED: succ-nn-ord
;;; PSS entry: theorem-library/succ-nn-ord.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'succ-nn-ord
  (lambda ()
    (sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (succ n) (succ_ORD n))))))
    (di)
    (mac 'ord-succ-nn)
    (rfl)))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: ord-segment-nn-succ
;;; PSS entry: theorem-library/ord-segment-nn-succ.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'ord-segment-nn-succ
  (lambda ()
    (sp (make-wff
         '(FORALL n (FORALL k (IMPLIES (IN n NN)
              (IFF (IN k (ORD-SEGMENT (succ n)))
                   (OR (IN k (ORD-SEGMENT n)) (= k n))))))))
    ;; (di) below peels FORALL n then FORALL k: eigenvars n_c and k_(c+1).
    (let ((n (eigen-name 'n *fresh-counter*))
          (k (eigen-name 'k (+ *fresh-counter* 1))))
      (di)                    ; peel FORALL n, FORALL k
      (di)                    ; move  n in nn  into the assumptions
      (mac 'succ-nn-ord)      ; succ(n) -> succ_ORD(n)
      (ta 'ord-segment-succ)
      (inst '(FORALL alpha (IMPLIES (IN alpha ORD)
                (FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD alpha)))
                               (OR (IN x (ORD-SEGMENT alpha)) (= x alpha))))))
            n)
      (cut `(FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD ,n)))
                           (OR (IN x (ORD-SEGMENT ,n)) (= x ,n)))))
      ;; Branch 1: prove the cut  FORALL x (IFF...)  by backchaining
      ;; ord-segment-succ, whose ORD hypothesis reduces to  n in NN.
      (bc `(IMPLIES (IN ,n ORD)
              (FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD ,n)))
                             (OR (IN x (ORD-SEGMENT ,n)) (= x ,n))))))
      (ta 'nn-subset-ord)
      (inst '(FORALL n (IMPLIES (IN n NN) (IN n ORD))) n)
      (bc `(IMPLIES (IN ,n NN) (IN ,n ORD)))
      (ass)
      ;; Branch 2: discharge the cut against the k instance.
      (inst `(FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD ,n)))
                            (OR (IN x (ORD-SEGMENT ,n)) (= x ,n))))
            k)
      (ass))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: ord-segment-zero-no-members
;;; PSS entry: theorem-library/ord-segment-zero-no-members.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'ord-segment-zero-no-members
  (lambda ()
    (sp (make-wff '(FORALL k (NOT (IN k (ORD-SEGMENT 0))))))
    (let ((k (eigen-name 'k *fresh-counter*)))
      (di)                         ; goal: NOT(IN k (ORD-SEGMENT 0))
      (mac 'ord-segment-zero)      ; ORD-SEGMENT(0) -> EMPTY-SET
      (ta 'empty-set-has-no-members)
      (inst '(FORALL x (NOT (IN x EMPTY-SET))) k)
      (ass))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: ord-segment-nn-subset
;;; PSS entry: theorem-library/ord-segment-nn-subset.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'ord-segment-nn-subset
  (lambda ()
    (sp (make-wff
         '(FORALL m (IMPLIES (IN m NN)
            (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN)))))))
    (ni)
    ;; base case  m = 0:  ORD-SEGMENT(0) is empty, so vacuous.
    (let ((k0 (eigen-name 'k *fresh-counter*)))
      (di)                         ; intro k, assume k in ORD-SEGMENT(0)
      (ta 'ord-segment-zero-no-members)
      (inst '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))) k0)
      (ai `(NOT (IN ,k0 (ORD-SEGMENT 0)))))
    ;; step case  m -> succ m
    (let ((mv (eigen-name 'm *fresh-counter*)))
      (di)                         ; intro m, hyp m in NN
      (di)                         ; assume IH
      (let ((kv (eigen-name 'k *fresh-counter*)))
        (di)                       ; intro k, assume k in ORD-SEGMENT(succ m)
        ;; cut the implication so the ORD-SEGMENT(succ m) membership sits in
        ;; goal-body position, where the ord-segment-nn-succ macete reaches it
        ;; (a bounded-forall domain restriction is not a rewritable subterm).
        (cut `(IMPLIES (IN ,kv (ORD-SEGMENT (succ ,mv))) (IN ,kv NN)))
        (let ((use-imp (last-node)))
          (mac 'ord-segment-nn-succ)   ; antecedent -> (k in os(m) or k = m)
          (di)                         ; assume (k in os(m) or k = m)
          (ai `(OR (IN ,kv (ORD-SEGMENT ,mv)) (= ,kv ,mv)))
          (let ((case2 (last-node)))
            ;; case 1: k in ORD-SEGMENT(m) -- use the IH
            (inst `(FORALL k (IMPLIES (IN k (ORD-SEGMENT ,mv)) (IN k NN))) kv)
            (bc `(IMPLIES (IN ,kv (ORD-SEGMENT ,mv)) (IN ,kv NN)))
            (ass)
            ;; case 2: k = m -- m in NN is in context
            (refocus! case2)
            (subst `(= ,kv ,mv))
            (ass))
          (refocus! use-imp)
          (bc `(IMPLIES (IN ,kv (ORD-SEGMENT (succ ,mv))) (IN ,kv NN)))
          (ass))))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: ord-segment-trans
;;; PSS entry: theorem-library/ord-segment-trans.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'ord-segment-trans
  (lambda ()
    (sp (make-wff
         '(FORALL m (IMPLIES (IN m NN)
            (FORALL k (FORALL i
              (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT m)))
                       (IN i (ORD-SEGMENT m)))))))))
    (ni)
    ;; base case  m = 0:  k in ORD-SEGMENT(0) is impossible
    (let ((kv (eigen-name 'k *fresh-counter*))
          (iv (eigen-name 'i (+ *fresh-counter* 1))))
      (di)                         ; intro k, i
      (di)                         ; assume the AND
      (ai `(AND (IN ,iv (ORD-SEGMENT ,kv)) (IN ,kv (ORD-SEGMENT 0))))
      (ta 'ord-segment-zero-no-members)
      (inst '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))) kv)
      (ai `(NOT (IN ,kv (ORD-SEGMENT 0)))))
    ;; step case  m -> succ m
    (let ((mv (eigen-name 'm *fresh-counter*)))
      (di)                         ; intro m, hyp m in NN
      (di)                         ; assume IH
      (let ((kv (eigen-name 'k *fresh-counter*))
            (iv (eigen-name 'i (+ *fresh-counter* 1))))
        (di)                       ; intro k, i
        (di)                       ; assume the AND
        (ai `(AND (IN ,iv (ORD-SEGMENT ,kv))
                  (IN ,kv (ORD-SEGMENT (succ ,mv)))))
        ;; cut the implication so k in os(succ m) sits in goal-body position
        (cut `(IMPLIES (IN ,kv (ORD-SEGMENT (succ ,mv)))
                       (IN ,iv (ORD-SEGMENT (succ ,mv)))))
        (let ((use-imp (last-node)))
          (mac 'ord-segment-nn-succ)    ; both k- and i-memberships rewritten
          (di)                          ; assume (k in os(m) or k = m)
          (ai `(OR (IN ,kv (ORD-SEGMENT ,mv)) (= ,kv ,mv)))
          (let ((case2 (last-node)))
            ;; case 1: k in ORD-SEGMENT(m) -- use the IH
            (oi-l)                      ; goal (OR ..) -> (IN i os(m))
            (inst `(FORALL k (FORALL i
                     (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT ,mv)))
                              (IN i (ORD-SEGMENT ,mv))))) kv)
            (inst `(FORALL i
                     (IMPLIES (AND (IN i (ORD-SEGMENT ,kv)) (IN ,kv (ORD-SEGMENT ,mv)))
                              (IN i (ORD-SEGMENT ,mv)))) iv)
            (bc `(IMPLIES (AND (IN ,iv (ORD-SEGMENT ,kv)) (IN ,kv (ORD-SEGMENT ,mv)))
                          (IN ,iv (ORD-SEGMENT ,mv))))
            (di)                        ; split the AND goal
            (let ((and2 (last-node)))
              (ass)                     ; (IN i os(k))
              (refocus! and2)
              (ass))                    ; (IN k os(m))
            ;; case 2: k = m
            (refocus! case2)
            (oi-l)                      ; goal -> (IN i os(m))
            (cut `(= ,mv ,kv))
            (let ((use-flip (last-node)))
              (subst `(= ,kv ,mv))
              (rfl)
              (refocus! use-flip)
              (subst `(= ,mv ,kv))      ; (IN i os(m)) -> (IN i os(k))
              (ass)))
          (refocus! use-imp)
          (bc `(IMPLIES (IN ,kv (ORD-SEGMENT (succ ,mv)))
                        (IN ,iv (ORD-SEGMENT (succ ,mv)))))
          (ass))))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: ord-segment-self
;;; PSS entry: theorem-library/ord-segment-self.scm
;;; ---------------------------------------------------------------------
(prove-and-install! 'ord-segment-self
  (lambda ()
    (sp (make-wff '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n)))))))
    (let ((nv (eigen-name 'n *fresh-counter*)))
      (di)                              ; intro n, assume n in NN
      ;; n in ORD -- the ord-segment-membership macete's side condition
      (ta 'nn-subset-ord)
      (inst '(FORALL n (IMPLIES (IN n NN) (IN n ORD))) nv)
      (cut `(IN ,nv ORD))
      (let ((use-ord (last-node)))
        (bc `(IMPLIES (IN ,nv NN) (IN ,nv ORD)))
        (ass)
        (refocus! use-ord)
        (mac 'ord-segment-membership)   ; (IN n os(n)) -> (<_ORD n n)
        (mac 'ord-lt-iff)               ; -> (AND (<=_ORD n n) (NOT (= n n)))
        (di)                            ; assume the AND, goal FALSITY
        (ai `(AND (<=_ORD ,nv ,nv) (NOT (= ,nv ,nv))))
        (cut `(= ,nv ,nv))
        (let ((use-eq (last-node)))
          (rfl)
          (refocus! use-eq)
          (ai `(NOT (= ,nv ,nv))))))))  ; not-elim closes FALSITY

;;; ---------------------------------------------------------------------
;;; ARCHIVED: enum-fam-in-fun
;;; PSS entry: theorem-library/enum-fam-in-fun.scm
;;; ---------------------------------------------------------------------
;;; enum-fam-in-fun:  ENUM-FAM(ag,f,phi,n) is a total function NN -> A(ag).
;;; The IF guard in ENUM-FAM fills indices outside ORD-SEGMENT(n) with E(ag),
;;; so the family is total even though the enumeration phi is only defined on
;;; ORD-SEGMENT(n).  This is the typing bridge: every SUM-AG lemma demands
;;; FUN(NN,A(ag)), and this is what supplies it.  Proof: lam-t reduces lambda
;;; membership to a FORALL; excluded-middle split on i in ORD-SEGMENT(n);
;;; if-true branch -> f(phi i) in A(ag) by fun-apply-type twice; if-false
;;; branch -> E(ag) in A(ag) by group-identity-in.
(prove-and-install! 'enum-fam-in-fun
  (lambda ()
    (sp (make-wff
         '(FORALL n (IMPLIES (IN n NN)
            (FORALL ag (IMPLIES (IS-GROUP ag)
            (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
            (FORALL f (IMPLIES (IN f (FUN S (A ag)))
              (IN (ENUM-FAM ag f phi n) (FUN NN (A ag))))))))))))))
    (define c0 *fresh-counter*)
    (define nv   (eigen-name 'n   c0))
    (define agv  (eigen-name 'ag  (+ c0 1)))
    (define Sv   (eigen-name 'S   (+ c0 2)))
    (define phiv (eigen-name 'phi (+ c0 3)))
    (define fv   (eigen-name 'f   (+ c0 4)))
    (di) (di) (di)
    (mac 'ENUM-FAM)
    (lam-t)
    (di)
    ;; the lambda eigenvar, read off the goal (IN (IF (IN iv ...) ...) (A ag))
    (define iv (cadr (cadr (cadr (wff-formula
                 (sequent-node-assertion (proof-state-focus *ps*)))))))
    (define P   `(IN ,iv (ORD-SEGMENT ,nv)))
    (define ifT `(IF ,P (,fv (,phiv ,iv)) (E ,agv)))

    ;; excluded middle on  P := iv in ORD-SEGMENT(n)
    (cut `(OR ,P (NOT ,P)))
    (define u-em (last-node))
      (pbc)
      (cut `(NOT ,P))
      (define u-em2 (last-node))
        (di)
        (cut `(OR ,P (NOT ,P)))
        (define u-em3 (last-node))
          (oi-l) (ass)
        (refocus! u-em3)
        (ai `(NOT (OR ,P (NOT ,P))))
      (refocus! u-em2)
      (cut `(OR ,P (NOT ,P)))
      (define u-em4 (last-node))
        (oi-r) (ass)
      (refocus! u-em4)
      (ai `(NOT (OR ,P (NOT ,P))))
    (refocus! u-em)
    (ai `(OR ,P (NOT ,P)))
    (define caseNP (last-node))

      ;; case P: iv in os(n) -- IF reduces to f(phi iv)
      (if-true ifT)
      (define u-pt (last-node))
        (ass)
      (refocus! u-pt)
      (subst `(= ,ifT (,fv (,phiv ,iv))))
      ;; phi iv in S
      (cut `(IN (,phiv ,iv) ,Sv))
      (define u-phiS (last-node))
        (ta 'fun-apply-type)
        (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                 (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) phiv)
        (inst `(FORALL A (FORALL B (FORALL x
                 (IMPLIES (AND (IN ,phiv (FUN A B)) (IN x A)) (IN (,phiv x) B)))))
              `(ORD-SEGMENT ,nv))
        (inst `(FORALL B (FORALL x
                 (IMPLIES (AND (IN ,phiv (FUN (ORD-SEGMENT ,nv) B))
                               (IN x (ORD-SEGMENT ,nv)))
                          (IN (,phiv x) B))))
              Sv)
        (inst `(FORALL x (IMPLIES (AND (IN ,phiv (FUN (ORD-SEGMENT ,nv) ,Sv))
                                       (IN x (ORD-SEGMENT ,nv)))
                                  (IN (,phiv x) ,Sv)))
              iv)
        (bc `(IMPLIES (AND (IN ,phiv (FUN (ORD-SEGMENT ,nv) ,Sv))
                           (IN ,iv (ORD-SEGMENT ,nv)))
                      (IN (,phiv ,iv) ,Sv)))
        (di)
        (define u-phiS2 (last-node))
          (ass)
        (refocus! u-phiS2)
          (ass)
      (refocus! u-phiS)
      ;; f(phi iv) in A(ag)
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) fv)
      (inst `(FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN ,fv (FUN A B)) (IN x A)) (IN (,fv x) B)))))
            Sv)
      (inst `(FORALL B (FORALL x
               (IMPLIES (AND (IN ,fv (FUN ,Sv B)) (IN x ,Sv)) (IN (,fv x) B))))
            `(A ,agv))
      (inst `(FORALL x (IMPLIES (AND (IN ,fv (FUN ,Sv (A ,agv))) (IN x ,Sv))
                                (IN (,fv x) (A ,agv))))
            `(,phiv ,iv))
      (bc `(IMPLIES (AND (IN ,fv (FUN ,Sv (A ,agv))) (IN (,phiv ,iv) ,Sv))
                    (IN (,fv (,phiv ,iv)) (A ,agv))))
      (di)
      (define u-fa (last-node))
        (ass)
      (refocus! u-fa)
        (ass)

    (refocus! caseNP)
      ;; case not-P: iv not in os(n) -- IF reduces to E(ag)
      (if-false ifT)
      (define u-pf (last-node))
        (ass)
      (refocus! u-pf)
      (subst `(= ,ifT (E ,agv)))
      ;; E(ag) in A(ag)
      (ta 'group-identity-in)
      (inst '(FORALL s (IMPLIES (IS-GROUP s) (IN (E s) (A s)))) agv)
      (bc `(IMPLIES (IS-GROUP ,agv) (IN (E ,agv) (A ,agv))))
      (ass)
))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: fin-enum-is-bijection
;;; PSS entry: theorem-library/fin-enum-is-bijection.scm
;;; ---------------------------------------------------------------------
;;; fin-enum-is-bijection:  FIN-ENUM(S) is a genuine bijection
;;; ORD-SEGMENT(CARD S) -> S when S is a finite set.  FIN-ENUM(S) is
;;; CHOICE of the BIJECTION class; card-finite-bij makes that class
;;; inhabited, so choice-axiom places the chosen element in it.
(prove-and-install! 'fin-enum-is-bijection
  (lambda ()
    (sp (make-wff
         '(FORALL S
            (IMPLIES (IN S SET)
            (IMPLIES (IN (CARD S) NN)
              (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S)))))))
    (define c0 *fresh-counter*)
    (define Sv (eigen-name 'S c0))
    (di) (di)
    (mac 'FIN-ENUM)
    (ta 'choice-axiom)
    (inst '(FORALL A (IMPLIES (FORSOME x (IN x A)) (IN (CHOICE A) A)))
          `(BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))
    (bc `(IMPLIES (FORSOME x (IN x (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv)))
                  (IN (CHOICE (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))
                      (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))))
    (ta 'card-finite-bij)
    (inst '(FORALL A (IMPLIES (AND (IN A SET) (IN (CARD A) NN))
              (FORSOME phi (IN phi (BIJECTION (ORD-SEGMENT (CARD A)) A)))))
          Sv)
    (bc `(IMPLIES (AND (IN ,Sv SET) (IN (CARD ,Sv) NN))
                  (FORSOME phi (IN phi (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv)))))
    (di)
    (define u-and (last-node))
      (ass)
    (refocus! u-and)
      (ass)
))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: finsum-well-defined
;;; PSS entry: theorem-library/finsum-well-defined.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; finsum-well-defined:  FINSUM(ag,f,S) does not depend on the enumeration.
;;;
;;; For any bijection enm : ORD-SEGMENT(CARD S) -> S, the sum of f along enm
;;; equals FINSUM(ag,f,S) -- which is the sum along the CHOICE-picked
;;; FIN-ENUM(S).  This frees later proofs from the CHOICE buried in FINSUM.
;;;
;;; Proof: mac FINSUM exposes both sides as SUM-AG over ENUM-FAM families;
;;; sum-ag-permutation-invariance equates them, with induced permutation
;;; psi = INVERSE-BIJ(FIN-ENUM S) o enm.  Its hypotheses are discharged as
;;; P3/P4 (ENUM-FAM in FUN(NN,A ag), via enum-fam-in-fun), P5 (psi a
;;; bijection, via bijection-compose + inverse-bij-is-bijection) and P6 (the
;;; families agree along psi, via ENUM-FAM unfold + inverse-bij-right).
;;; Developed in prover/scratch-finsum.scm.
(prove-and-install! 'finsum-well-defined
  (lambda ()
    (define (S v t f) (subst-free v t f))

    (define fwd-goal
      '(FORALL S
         (IMPLIES (IN S SET)
         (IMPLIES (IN (CARD S) NN)
         (FORALL ag
         (IMPLIES (IS-ABELIAN-GROUP ag)
         (FORALL f
         (IMPLIES (IN f (FUN S (A ag)))
         (FORALL enm
         (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT (CARD S)) S))
           (= (FINSUM ag f S)
              (SUM-AG ag (ENUM-FAM ag f enm (CARD S)) (CARD S)))))))))))))

    (define PI
      '(FORALL n
         (IMPLIES (IN n NN)
         (FORALL ag
         (IMPLIES (IS-ABELIAN-GROUP ag)
         (FORALL g
         (IMPLIES (IN g (FUN NN (A ag)))
         (FORALL h
         (IMPLIES (IN h (FUN NN (A ag)))
         (FORALL phi
         (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
         (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
           (= (SUM-AG ag g n) (SUM-AG ag h n))))))))))))))

    (sp (make-wff fwd-goal))
    (define c0 *fresh-counter*)
    (define Sv   (eigen-name 'S   c0))
    (define agv  (eigen-name 'ag  (+ c0 1)))
    (define fv   (eigen-name 'f   (+ c0 2)))
    (define enmv (eigen-name 'enm (+ c0 3)))
    (di)(di)(di)(di)(di)
    (mac 'FINSUM)

    ;; term abbreviations
    (define n     `(CARD ,Sv))
    (define osn   `(ORD-SEGMENT (CARD ,Sv)))
    (define feS   `(FIN-ENUM ,Sv))
    (define G     `(ENUM-FAM ,agv ,fv ,feS (CARD ,Sv)))
    (define H     `(ENUM-FAM ,agv ,fv ,enmv (CARD ,Sv)))
    (define invfe `(INVERSE-BIJ ,feS ,osn ,Sv))
    (define psi   `(VNB-LAMBDA i (,invfe (,enmv i))))

    ;; instantiation intermediates for perm-invariance
    (define PIn   (S 'n n (caddr PI)))
    (define X1    (caddr PIn))
    (define PIag  (S 'ag agv (caddr X1)))
    (define X2    (caddr PIag))
    (define PIg   (S 'g G (caddr X2)))
    (define X3    (caddr PIg))
    (define PIh   (S 'h H (caddr X3)))
    (define X4    (caddr PIh))
    (define PIphi (S 'phi psi (caddr X4)))
    (define X5    (caddr PIphi))

    ;; enum-fam-in-fun instantiation chain (P3 = G, P4 = H).  EF alternates
    ;; FORALL/IMPLIES except for the consecutive FORALL S / FORALL phi pair.
    (define EF '(FORALL n (IMPLIES (IN n NN)
       (FORALL ag (IMPLIES (IS-GROUP ag)
       (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
       (FORALL f (IMPLIES (IN f (FUN S (A ag)))
         (IN (ENUM-FAM ag f phi n) (FUN NN (A ag)))))))))))))
    (define EFn  (S 'n n (caddr EF)))
    (define EX1  (caddr EFn))
    (define EFag (S 'ag agv (caddr EX1)))
    (define EX2  (caddr EFag))
    (define EFS  (S 'S Sv (caddr EX2)))
    (define EFphi  (S 'phi feS (caddr EFS)))   ; phi := FIN-ENUM(S)  (P3)
    (define EX3    (caddr EFphi))
    (define EFf    (S 'f fv (caddr EX3)))
    (define EFphiB (S 'phi enmv (caddr EFS)))  ; phi := enm  (P4)
    (define EX3B   (caddr EFphiB))
    (define EFfB   (S 'f fv (caddr EX3B)))

    ;; bijection-compose instantiation chain (P5).
    (define BJC '(FORALL X (FORALL Y (FORALL Z (FORALL phi (FORALL psi
       (IMPLIES (AND (IN phi (BIJECTION X Y))
                     (IN psi (BIJECTION Y Z)))
                (IN (VNB-LAMBDA x_ (psi (phi x_)))
                    (BIJECTION X Z)))))))))
    (define BJC1 (S 'X osn (caddr BJC)))
    (define BJC2 (S 'Y Sv  (caddr BJC1)))
    (define BJC3 (S 'Z osn (caddr BJC2)))
    (define BJC4 (S 'phi enmv (caddr BJC3)))
    (define BJC5 (S 'psi invfe (caddr BJC4)))

    ;; reusable sub-proofs (operate on the current focus)
    ;; goal: (IN feS (BIJECTION osn Sv))
    (define (feb-inline)
      (ta 'fin-enum-is-bijection)
      (inst '(FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
                (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S))))) Sv)
      (cut `(IMPLIES (IN (CARD ,Sv) NN)
               (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))))
      (let ((u (last-node)))
        (bc `(IMPLIES (IN ,Sv SET)
                (IMPLIES (IN (CARD ,Sv) NN)
                   (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv)))))
        (ass)
        (refocus! u)
        (bc `(IMPLIES (IN (CARD ,Sv) NN)
                (IN (FIN-ENUM ,Sv) (BIJECTION (ORD-SEGMENT (CARD ,Sv)) ,Sv))))
        (ass)))
    ;; goal: (IS-GROUP agv)
    (define (isg-inline)
      (ta 'abelian-group-is-group)
      (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) agv)
      (bc `(IMPLIES (IS-ABELIAN-GROUP ,agv) (IS-GROUP ,agv)))
      (ass))
    ;; goal: (IN pt (FUN osn Sv)) -- reduced to (IN pt (BIJECTION osn Sv))
    (define (bij-in-fun-inline pt)
      (ta 'bijection-in-fun)
      (inst '(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))) osn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn Y)) (IN phi (FUN ,osn Y))))) Sv)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn ,Sv)) (IN phi (FUN ,osn ,Sv)))) pt)
      (bc `(IMPLIES (IN ,pt (BIJECTION ,osn ,Sv)) (IN ,pt (FUN ,osn ,Sv)))))

    ;; main: apply sum-ag-permutation-invariance, then close P3-P6.
    (ta 'sum-ag-permutation-invariance)
    (inst PI n)
    (cut X1) (define uX1 (last-node)) (bc PIn) (ass) (refocus! uX1)
    (inst X1 agv)
    (cut X2) (define uX2 (last-node)) (bc PIag) (ass) (refocus! uX2)
    (inst X2 G)
    (cut X3) (define uX3 (last-node)) (bc PIg)

    ;; P3: G = ENUM-FAM(ag,f,FIN-ENUM(S),CARD S) in FUN(NN, A(ag))
    (ta 'enum-fam-in-fun)
    (inst EF n)
    (cut EX1) (define uE1 (last-node)) (bc EFn) (ass) (refocus! uE1)
    (inst EX1 agv)
    (cut EX2) (define uE2 (last-node)) (bc EFag) (isg-inline) (refocus! uE2)
    (inst EX2 Sv)
    (inst EFS feS)
    (cut EX3) (define uE3 (last-node)) (bc EFphi)
      (bij-in-fun-inline feS)
      (feb-inline)
    (refocus! uE3)
    (inst EX3 fv)
    (bc EFf) (ass)

    (refocus! uX3)
    (inst X3 H)
    (cut X4) (define uX4 (last-node)) (bc PIh)

    ;; P4: H = ENUM-FAM(ag,f,enm,CARD S) in FUN(NN, A(ag))
    (ta 'enum-fam-in-fun)
    (inst EF n)
    (cut EX1) (define uF1 (last-node)) (bc EFn) (ass) (refocus! uF1)
    (inst EX1 agv)
    (cut EX2) (define uF2 (last-node)) (bc EFag) (isg-inline) (refocus! uF2)
    (inst EX2 Sv)
    (inst EFS enmv)
    (cut EX3B) (define uF3 (last-node)) (bc EFphiB)
      (bij-in-fun-inline enmv)
      (ass)                       ; enm in BIJECTION(osn, Sv) -- hypothesis
    (refocus! uF3)
    (inst EX3B fv)
    (bc EFfB) (ass)

    (refocus! uX4)
    (inst X4 psi)
    (cut X5) (define uX5 (last-node)) (bc PIphi)

    ;; P5: psi = INVERSE-BIJ(FIN-ENUM(S)) o enm is a bijection.  Proved with
    ;; the lambda bound by x_ (matching bijection-compose); the cut closes the
    ;; i-bound goal by alpha-equivalence.
    (cut `(IN (VNB-LAMBDA x_ (,invfe (,enmv x_))) (BIJECTION ,osn ,osn)))
    (define uP5 (last-node))
      (ta 'bijection-compose)
      (inst BJC osn) (inst BJC1 Sv) (inst BJC2 osn) (inst BJC3 enmv) (inst BJC4 invfe)
      (bc BJC5)
      (di)
      (define p5and2 (last-node))
        (ass)                     ; enm in BIJECTION(osn, Sv) -- hypothesis
      (refocus! p5and2)
        (ta 'inverse-bij-is-bijection)
        (inst '(FORALL X (FORALL Y (FORALL phi
                  (IMPLIES (IN phi (BIJECTION X Y))
                           (IN (INVERSE-BIJ phi X Y) (BIJECTION Y X)))))) osn)
        (inst `(FORALL Y (FORALL phi
                  (IMPLIES (IN phi (BIJECTION ,osn Y))
                           (IN (INVERSE-BIJ phi ,osn Y) (BIJECTION Y ,osn))))) Sv)
        (inst `(FORALL phi
                  (IMPLIES (IN phi (BIJECTION ,osn ,Sv))
                           (IN (INVERSE-BIJ phi ,osn ,Sv) (BIJECTION ,Sv ,osn)))) feS)
        (bc `(IMPLIES (IN ,feS (BIJECTION ,osn ,Sv))
                      (IN ,invfe (BIJECTION ,Sv ,osn))))
        (feb-inline)
    (refocus! uP5)
    (ass)

    (refocus! uX5)
    (bc X5)

    ;; P6: agreement  H(i) = G(psi(i))  for i in ORD-SEGMENT(CARD S).
    (cut `(IN ,feS (BIJECTION ,osn ,Sv)))     ; FACT-feS, shared below
    (define u6feS (last-node))
      (feb-inline)
    (refocus! u6feS)

    (define p6c *fresh-counter*)
    (define iv (eigen-name 'i p6c))
    (di)                           ; peel FORALL i
    (di)                           ; assume (IN iv osn)

    ;; FACT-eiv: enm(iv) in Sv
    (cut `(IN (,enmv ,iv) ,Sv))
    (define u6eiv (last-node))
      (cut `(IN ,enmv (FUN ,osn ,Sv)))
      (define u6efun (last-node))
        (bij-in-fun-inline enmv)
        (ass)
      (refocus! u6efun)
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) enmv)
      (inst `(FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN ,enmv (FUN A B)) (IN x A)) (IN (,enmv x) B))))) osn)
      (inst `(FORALL B (FORALL x
                (IMPLIES (AND (IN ,enmv (FUN ,osn B)) (IN x ,osn)) (IN (,enmv x) B)))) Sv)
      (inst `(FORALL x (IMPLIES (AND (IN ,enmv (FUN ,osn ,Sv)) (IN x ,osn))
                                (IN (,enmv x) ,Sv))) iv)
      (bc `(IMPLIES (AND (IN ,enmv (FUN ,osn ,Sv)) (IN ,iv ,osn))
                    (IN (,enmv ,iv) ,Sv)))
      (di)
      (define u6eiv2 (last-node))
        (ass)
      (refocus! u6eiv2)
        (ass)
    (refocus! u6eiv)

    ;; FACT-ivfun: invfe in FUN(Sv, osn)
    (cut `(IN ,invfe (FUN ,Sv ,osn)))
    (define u6ivfun (last-node))
      (ta 'inverse-bij-in-fun)
      (inst '(FORALL X (FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION X Y))
                         (IN (INVERSE-BIJ phi X Y) (FUN Y X)))))) osn)
      (inst `(FORALL Y (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn Y))
                         (IN (INVERSE-BIJ phi ,osn Y) (FUN Y ,osn))))) Sv)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn ,Sv))
                         (IN (INVERSE-BIJ phi ,osn ,Sv) (FUN ,Sv ,osn)))) feS)
      (bc `(IMPLIES (IN ,feS (BIJECTION ,osn ,Sv)) (IN ,invfe (FUN ,Sv ,osn))))
      (ass)
    (refocus! u6ivfun)

    ;; unfold ENUM-FAM on both sides and beta-reduce
    (mac 'ENUM-FAM)
    (lam-b)

    ;; LHS: IF (IN iv osn) (f (enm iv)) (E ag) -- condition holds
    (if-true `(IF (IN ,iv ,osn) (,fv (,enmv ,iv)) (E ,agv)))
    (define u6lt (last-node))
      (ass)
    (refocus! u6lt)
    (subst `(= (IF (IN ,iv ,osn) (,fv (,enmv ,iv)) (E ,agv)) (,fv (,enmv ,iv))))

    ;; RHS: IF (IN (invfe (enm iv)) osn) (f (feS (invfe (enm iv)))) (E ag)
    (if-true `(IF (IN (,invfe (,enmv ,iv)) ,osn)
                  (,fv (,feS (,invfe (,enmv ,iv)))) (E ,agv)))
    (define u6rt (last-node))
      (ta 'fun-apply-type)              ; (IN (invfe (enm iv)) osn)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) invfe)
      (inst `(FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN ,invfe (FUN A B)) (IN x A)) (IN (,invfe x) B))))) Sv)
      (inst `(FORALL B (FORALL x
                (IMPLIES (AND (IN ,invfe (FUN ,Sv B)) (IN x ,Sv)) (IN (,invfe x) B)))) osn)
      (inst `(FORALL x (IMPLIES (AND (IN ,invfe (FUN ,Sv ,osn)) (IN x ,Sv))
                                (IN (,invfe x) ,osn))) `(,enmv ,iv))
      (bc `(IMPLIES (AND (IN ,invfe (FUN ,Sv ,osn)) (IN (,enmv ,iv) ,Sv))
                    (IN (,invfe (,enmv ,iv)) ,osn)))
      (di)
      (define u6rt2 (last-node))
        (ass)
      (refocus! u6rt2)
        (ass)
    (refocus! u6rt)
    (subst `(= (IF (IN (,invfe (,enmv ,iv)) ,osn)
                   (,fv (,feS (,invfe (,enmv ,iv)))) (E ,agv))
               (,fv (,feS (,invfe (,enmv ,iv))))))

    ;; goal: (= (f (enm iv)) (f (feS (invfe (enm iv)))))
    ;; feS(invfe(enm iv)) = enm iv  by inverse-bij-right
    (cut `(= (,feS (,invfe (,enmv ,iv))) (,enmv ,iv)))
    (define u6ibr (last-node))
      (ta 'inverse-bij-right)
      (inst '(FORALL dom (FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION dom cod))
                  (FORALL y (IMPLIES (IN y cod)
                    (= (phi ((INVERSE-BIJ phi dom cod) y)) y))))))) osn)
      (inst `(FORALL cod (FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn cod))
                  (FORALL y (IMPLIES (IN y cod)
                    (= (phi ((INVERSE-BIJ phi ,osn cod) y)) y)))))) Sv)
      (inst `(FORALL phi
                (IMPLIES (IN phi (BIJECTION ,osn ,Sv))
                  (FORALL y (IMPLIES (IN y ,Sv)
                    (= (phi ((INVERSE-BIJ phi ,osn ,Sv) y)) y))))) feS)
      (cut `(FORALL y (IMPLIES (IN y ,Sv)
               (= (,feS ((INVERSE-BIJ ,feS ,osn ,Sv) y)) y))))
      (define u6ibr2 (last-node))
        (bc `(IMPLIES (IN ,feS (BIJECTION ,osn ,Sv))
                (FORALL y (IMPLIES (IN y ,Sv)
                  (= (,feS ((INVERSE-BIJ ,feS ,osn ,Sv) y)) y)))))
        (ass)
      (refocus! u6ibr2)
      (inst `(FORALL y (IMPLIES (IN y ,Sv)
                (= (,feS ((INVERSE-BIJ ,feS ,osn ,Sv) y)) y))) `(,enmv ,iv))
      (bc `(IMPLIES (IN (,enmv ,iv) ,Sv)
              (= (,feS ((INVERSE-BIJ ,feS ,osn ,Sv) (,enmv ,iv))) (,enmv ,iv))))
      (ass)
    (refocus! u6ibr)
    (subst `(= (,feS (,invfe (,enmv ,iv))) (,enmv ,iv)))
    (rfl)))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: union-empty-left
;;; PSS entry: theorem-library/union-empty-left.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; union-empty-left:  UNION(EMPTY-SET, A) = A  for A a set.
;;; Set extensionality (a macete on the goal equality) reduces it to the
;;; membership iff; union-membership unfolds the union; the empty disjunct
;;; is killed by empty-set-has-no-members.
(prove-and-install! 'union-empty-left
  (lambda ()
    (sp (make-wff '(FORALL A (IMPLIES (IN A SET) (= (UNION EMPTY-SET A) A)))))
    (let ((Av (eigen-name 'A *fresh-counter*)))
      (di)
      (cut `(IN (UNION EMPTY-SET ,Av) SET))
      (let ((u-clo (last-node)))
        (ta 'union-set-closure)
        (inst '(FORALL A (FORALL B (IMPLIES (AND (IN A SET) (IN B SET))
                                            (IN (UNION A B) SET)))) 'EMPTY-SET)
        (inst `(FORALL B (IMPLIES (AND (IN EMPTY-SET SET) (IN B SET))
                                  (IN (UNION EMPTY-SET B) SET))) Av)
        (bc `(IMPLIES (AND (IN EMPTY-SET SET) (IN ,Av SET))
                      (IN (UNION EMPTY-SET ,Av) SET)))
        (di)
        (let ((u-and1 (last-node)))
          (ta 'empty-set-is-set) (ass)
          (refocus! u-and1)
          (ass))
        (refocus! u-clo))
      (mac 'extensionality)
      (let ((xv (eigen-name 'x *fresh-counter*)))
        (di)
        (mac 'union-membership)
        (di)
        (let ((iff-back (last-node)))
          (ai `(OR (IN ,xv EMPTY-SET) (IN ,xv ,Av)))
          (let ((or-c2 (last-node)))
            (ta 'empty-set-has-no-members)
            (inst '(FORALL x (NOT (IN x EMPTY-SET))) xv)
            (ai `(NOT (IN ,xv EMPTY-SET)))
            (refocus! or-c2)
            (ass))
          (refocus! iff-back)
          (oi-r)
          (ass))))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: finsum-empty
;;; PSS entry: theorem-library/finsum-empty.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; finsum-empty:  FINSUM(ag, f, EMPTY-SET) = E(ag).
;;; mac FINSUM exposes SUM-AG over CARD(EMPTY-SET); card-empty rewrites that
;;; to 0; sum-ag-zero collapses the empty sum to the identity.
(prove-and-install! 'finsum-empty
  (lambda ()
    (sp (make-wff '(FORALL ag (FORALL f (= (FINSUM ag f EMPTY-SET) (E ag))))))
    (di) (di)
    (mac 'FINSUM)
    (mac 'card-empty)
    (mac 'sum-ag-zero)
    (rfl)))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: card-singleton
;;; PSS entry: theorem-library/card-singleton.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; card-singleton:  CARD(PAIR x x) = succ 0  for x a set.
;;; PAIR x x is the singleton {x}.  card-insert at A := EMPTY-SET gives
;;; CARD(UNION EMPTY-SET (PAIR x x)) = succ_ORD(CARD EMPTY-SET);
;;; union-empty-left collapses the union, card-empty the inner CARD, and
;;; ord-succ-nn turns succ_ORD 0 into succ 0 (so no 1 = succ 0 bridge is
;;; needed -- downstream SUM-AG reductions stay in succ form).
(prove-and-install! 'card-singleton
  (lambda ()
    (sp (make-wff '(FORALL x (IMPLIES (IN x SET)
                     (= (CARD (PAIR x x)) (succ 0))))))
    (let ((xc (eigen-name 'x *fresh-counter*)))
      (di)
      ;; FACT-pset: (IN (PAIR xc xc) SET)
      (cut `(IN (PAIR ,xc ,xc) SET))
      (let ((u-pset (last-node)))
        (ta 'pairing)
        (inst '(FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
                                            (IN (PAIR a b) SET)))) xc)
        (inst `(FORALL b (IMPLIES (AND (IN ,xc SET) (IN b SET))
                                  (IN (PAIR ,xc b) SET))) xc)
        (bc `(IMPLIES (AND (IN ,xc SET) (IN ,xc SET)) (IN (PAIR ,xc ,xc) SET)))
        (di)
        (let ((u-pand (last-node)))
          (ass)
          (refocus! u-pand)
          (ass))
        (refocus! u-pset))
      ;; FACT-ue: (= (UNION EMPTY-SET (PAIR xc xc)) (PAIR xc xc))
      (cut `(= (UNION EMPTY-SET (PAIR ,xc ,xc)) (PAIR ,xc ,xc)))
      (let ((u-ue (last-node)))
        (ta 'union-empty-left)
        (inst '(FORALL A (IMPLIES (IN A SET) (= (UNION EMPTY-SET A) A)))
              `(PAIR ,xc ,xc))
        (bc `(IMPLIES (IN (PAIR ,xc ,xc) SET)
                      (= (UNION EMPTY-SET (PAIR ,xc ,xc)) (PAIR ,xc ,xc))))
        (ass)
        (refocus! u-ue))
      ;; FACT-ci: card-insert at A := EMPTY-SET, x := xc
      (cut `(= (CARD (UNION EMPTY-SET (PAIR ,xc ,xc))) (succ_ORD (CARD EMPTY-SET))))
      (let ((u-ci (last-node)))
        (ta 'card-insert)
        (inst '(FORALL A (IMPLIES (IN A SET)
                  (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x A)))
                    (= (CARD (UNION A (PAIR x x))) (succ_ORD (CARD A)))))))
              'EMPTY-SET)
        (cut `(FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x EMPTY-SET)))
                (= (CARD (UNION EMPTY-SET (PAIR x x))) (succ_ORD (CARD EMPTY-SET))))))
        (let ((u-ci2 (last-node)))
          (bc `(IMPLIES (IN EMPTY-SET SET)
                  (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x EMPTY-SET)))
                    (= (CARD (UNION EMPTY-SET (PAIR x x)))
                       (succ_ORD (CARD EMPTY-SET)))))))
          (ta 'empty-set-is-set) (ass)
          (refocus! u-ci2))
        (inst `(FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x EMPTY-SET)))
                  (= (CARD (UNION EMPTY-SET (PAIR x x))) (succ_ORD (CARD EMPTY-SET)))))
              xc)
        (bc `(IMPLIES (AND (IN ,xc SET) (NOT (IN ,xc EMPTY-SET)))
                (= (CARD (UNION EMPTY-SET (PAIR ,xc ,xc)))
                   (succ_ORD (CARD EMPTY-SET)))))
        (di)
        (let ((u-ciand (last-node)))
          (ass)
          (refocus! u-ciand)
          (ta 'empty-set-has-no-members)
          (inst '(FORALL x (NOT (IN x EMPTY-SET))) xc)
          (ass))
        (refocus! u-ci))
      ;; FACT-on: (= (succ_ORD 0) (succ 0))
      (cut `(= (succ_ORD 0) (succ 0)))
      (let ((u-on (last-node)))
        (ta 'ord-succ-nn)
        (inst '(FORALL n (IMPLIES (IN n NN) (= (succ_ORD n) (succ n)))) '0)
        (bc '(IMPLIES (IN 0 NN) (= (succ_ORD 0) (succ 0))))
        (ta 'nn-zero-in) (ass)
        (refocus! u-on))
      ;; assemble
      (cut `(= (PAIR ,xc ,xc) (UNION EMPTY-SET (PAIR ,xc ,xc))))
      (let ((u-flip (last-node)))
        (subst `(= (UNION EMPTY-SET (PAIR ,xc ,xc)) (PAIR ,xc ,xc)))
        (rfl)
        (refocus! u-flip))
      (subst `(= (PAIR ,xc ,xc) (UNION EMPTY-SET (PAIR ,xc ,xc))))
      (subst `(= (CARD (UNION EMPTY-SET (PAIR ,xc ,xc))) (succ_ORD (CARD EMPTY-SET))))
      (mac 'card-empty)
      (subst `(= (succ_ORD 0) (succ 0)))
      (rfl))))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: finsum-singleton
;;; PSS entry: theorem-library/finsum-singleton.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; finsum-singleton:  FINSUM(ag, f, PAIR x x) = f(x).
;;;
;;; PAIR x x is the singleton {x}.  mac FINSUM exposes the SUM-AG; card-singleton
;;; rewrites CARD(PAIR x x) to succ 0, so sum-ag-succ + sum-ag-zero collapse
;;; the one-term sum to (MUL ag)(E ag, G(0)), and group-left-id strips the
;;; identity.  G(0) = f(x) (FACT-G0): unfold ENUM-FAM + beta + if-true gives
;;; f(FIN-ENUM(PAIR x x)(0)); FIN-ENUM(PAIR x x)(0) in PAIR x x (it is a
;;; bijection), and pairing-membership forces that element to be x.
;;; Developed in prover/scratch-fs2.scm.
(prove-and-install! 'finsum-singleton
  (lambda ()
    (sp (make-wff
         '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
            (FORALL x (IMPLIES (IN x SET)
            (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (A ag)))
              (= (FINSUM ag f (PAIR x x)) (f x))))))))))
    (define c0 *fresh-counter*)
    (define agv (eigen-name 'ag c0))
    (define xv  (eigen-name 'x  (+ c0 1)))
    (define fv  (eigen-name 'f  (+ c0 2)))
    (di) (di) (di) (di)
    (define FE `(FIN-ENUM (PAIR ,xv ,xv)))

    ;; ---- shared facts ----
    ;; FACT-pset: (IN (PAIR xv xv) SET)
    (cut `(IN (PAIR ,xv ,xv) SET))
    (define u-ps (last-node))
      (ta 'pairing)
      (inst '(FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
                                          (IN (PAIR a b) SET)))) xv)
      (inst `(FORALL b (IMPLIES (AND (IN ,xv SET) (IN b SET))
                                (IN (PAIR ,xv b) SET))) xv)
      (bc `(IMPLIES (AND (IN ,xv SET) (IN ,xv SET)) (IN (PAIR ,xv ,xv) SET)))
      (di)
      (define u-psa (last-node))
        (ass)
      (refocus! u-psa)
        (ass)
    (refocus! u-ps)

    ;; CSI: (= (CARD (PAIR xv xv)) (succ 0))
    (cut `(= (CARD (PAIR ,xv ,xv)) (succ 0)))
    (define u-csi (last-node))
      (ta 'card-singleton)
      (inst '(FORALL x (IMPLIES (IN x SET) (= (CARD (PAIR x x)) (succ 0)))) xv)
      (bc `(IMPLIES (IN ,xv SET) (= (CARD (PAIR ,xv ,xv)) (succ 0))))
      (ass)
    (refocus! u-csi)

    ;; CSI-rev: (= (succ 0) (CARD (PAIR xv xv)))
    (cut `(= (succ 0) (CARD (PAIR ,xv ,xv))))
    (define u-csir (last-node))
      (subst `(= (CARD (PAIR ,xv ,xv)) (succ 0)))
      (rfl)
    (refocus! u-csir)

    ;; FACT-snn: (IN (succ 0) NN)
    (cut `(IN (succ 0) NN))
    (define u-snn (last-node))
      (ta 'nn-succ-closed)
      (inst '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))) '0)
      (bc '(IMPLIES (IN 0 NN) (IN (succ 0) NN)))
      (ta 'nn-zero-in) (ass)
    (refocus! u-snn)

    ;; FACT-isg: (IS-GROUP agv)
    (cut `(IS-GROUP ,agv))
    (define u-isg (last-node))
      (ta 'abelian-group-is-group)
      (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) agv)
      (bc `(IMPLIES (IS-ABELIAN-GROUP ,agv) (IS-GROUP ,agv)))
      (ass)
    (refocus! u-isg)

    ;; FACT-0os: (IN 0 (ORD-SEGMENT (succ 0)))
    (cut `(IN 0 (ORD-SEGMENT (succ 0))))
    (define u-0os (last-node))
      (ta 'nn-zero-in)
      (mac 'ord-segment-nn-succ)
      (oi-r)
      (rfl)
    (refocus! u-0os)

    ;; FACT-xin: (IN xv (PAIR xv xv))
    (cut `(IN ,xv (PAIR ,xv ,xv)))
    (define u-xin (last-node))
      (mac 'pairing-membership)
      (oi-l)
      (rfl)
    (refocus! u-xin)

    ;; ---- main reduction ----
    (mac 'FINSUM)
    (subst `(= (CARD (PAIR ,xv ,xv)) (succ 0)))
    (ta 'nn-zero-in)
    (mac 'sum-ag-succ)
    (mac 'sum-ag-zero)
    ;; goal: (= ((MUL agv) (E agv) ((ENUM-FAM agv fv FE (succ 0)) 0)) (fv xv))

    ;; FACT-G0: ((ENUM-FAM agv fv FE (succ 0)) 0) = (fv xv)
    (cut `(= ((ENUM-FAM ,agv ,fv ,FE (succ 0)) 0) (,fv ,xv)))
    (define u-g0 (last-node))
      (mac 'ENUM-FAM)
      (lam-b)
      (if-true `(IF (IN 0 (ORD-SEGMENT (succ 0))) (,fv (,FE 0)) (E ,agv)))
      (define u-it (last-node))
        (ass)
      (refocus! u-it)
      (subst `(= (IF (IN 0 (ORD-SEGMENT (succ 0))) (,fv (,FE 0)) (E ,agv))
                 (,fv (,FE 0))))
      ;; goal: (= (fv (FE 0)) (fv xv)) ; need (= (FE 0) xv)
      (cut `(= (,FE 0) ,xv))
      (define u-fe0 (last-node))
        ;; cut-implication trick: (IN (FE 0)(PAIR xv xv)) -> (= (FE 0) xv)
        (cut `(IMPLIES (IN (,FE 0) (PAIR ,xv ,xv)) (= (,FE 0) ,xv)))
        (define u-pimp (last-node))
          (mac 'pairing-membership)
          (di)
          (ai `(OR (= (,FE 0) ,xv) (= (,FE 0) ,xv)))
          (define u-orc2 (last-node))
            (ass)
          (refocus! u-orc2)
            (ass)
        (refocus! u-pimp)
        (bc `(IMPLIES (IN (,FE 0) (PAIR ,xv ,xv)) (= (,FE 0) ,xv)))
        ;; goal: (IN (FE 0) (PAIR xv xv))
        (cut `(IN ,FE (FUN (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv))))
        (define u-fefun (last-node))
          (cut `(IN ,FE (BIJECTION (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv))))
          (define u-febij (last-node))
            (subst `(= (succ 0) (CARD (PAIR ,xv ,xv))))
            (ta 'fin-enum-is-bijection)
            (inst '(FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
                      (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S)))))
                  `(PAIR ,xv ,xv))
            (cut `(IMPLIES (IN (CARD (PAIR ,xv ,xv)) NN)
                    (IN (FIN-ENUM (PAIR ,xv ,xv))
                        (BIJECTION (ORD-SEGMENT (CARD (PAIR ,xv ,xv)))
                                   (PAIR ,xv ,xv)))))
            (define u-feb2 (last-node))
              (bc `(IMPLIES (IN (PAIR ,xv ,xv) SET)
                      (IMPLIES (IN (CARD (PAIR ,xv ,xv)) NN)
                        (IN (FIN-ENUM (PAIR ,xv ,xv))
                            (BIJECTION (ORD-SEGMENT (CARD (PAIR ,xv ,xv)))
                                       (PAIR ,xv ,xv))))))
              (ass)
            (refocus! u-feb2)
            (bc `(IMPLIES (IN (CARD (PAIR ,xv ,xv)) NN)
                    (IN (FIN-ENUM (PAIR ,xv ,xv))
                        (BIJECTION (ORD-SEGMENT (CARD (PAIR ,xv ,xv)))
                                   (PAIR ,xv ,xv)))))
            (subst `(= (CARD (PAIR ,xv ,xv)) (succ 0)))
            (ass)
          (refocus! u-febij)
          (ta 'bijection-in-fun)
          (inst '(FORALL X (FORALL Y (FORALL phi
                    (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y))))))
                `(ORD-SEGMENT (succ 0)))
          (inst `(FORALL Y (FORALL phi
                    (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT (succ 0)) Y))
                             (IN phi (FUN (ORD-SEGMENT (succ 0)) Y)))))
                `(PAIR ,xv ,xv))
          (inst `(FORALL phi
                    (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT (succ 0))
                                                (PAIR ,xv ,xv)))
                             (IN phi (FUN (ORD-SEGMENT (succ 0))
                                          (PAIR ,xv ,xv)))))
                FE)
          (bc `(IMPLIES (IN ,FE (BIJECTION (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv)))
                        (IN ,FE (FUN (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv)))))
          (ass)
        (refocus! u-fefun)
        (ta 'fun-apply-type)
        (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                  (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) FE)
        (inst `(FORALL A (FORALL B (FORALL x
                  (IMPLIES (AND (IN ,FE (FUN A B)) (IN x A)) (IN (,FE x) B)))))
              `(ORD-SEGMENT (succ 0)))
        (inst `(FORALL B (FORALL x
                  (IMPLIES (AND (IN ,FE (FUN (ORD-SEGMENT (succ 0)) B))
                                (IN x (ORD-SEGMENT (succ 0))))
                           (IN (,FE x) B))))
              `(PAIR ,xv ,xv))
        (inst `(FORALL x (IMPLIES
                  (AND (IN ,FE (FUN (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv)))
                       (IN x (ORD-SEGMENT (succ 0))))
                  (IN (,FE x) (PAIR ,xv ,xv)))) '0)
        (bc `(IMPLIES (AND (IN ,FE (FUN (ORD-SEGMENT (succ 0)) (PAIR ,xv ,xv)))
                           (IN 0 (ORD-SEGMENT (succ 0))))
                      (IN (,FE 0) (PAIR ,xv ,xv))))
        (di)
        (define u-fat (last-node))
          (ass)
        (refocus! u-fat)
          (ass)
      (refocus! u-fe0)
      (subst `(= (,FE 0) ,xv))
      (rfl)
    (refocus! u-g0)
    (subst `(= ((ENUM-FAM ,agv ,fv ,FE (succ 0)) 0) (,fv ,xv)))
    ;; goal: (= ((MUL agv) (E agv) (fv xv)) (fv xv))

    ;; FACT-fxa: (IN (fv xv) (A agv))
    (cut `(IN (,fv ,xv) (A ,agv)))
    (define u-fxa (last-node))
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) fv)
      (inst `(FORALL A (FORALL B (FORALL x
                (IMPLIES (AND (IN ,fv (FUN A B)) (IN x A)) (IN (,fv x) B)))))
            `(PAIR ,xv ,xv))
      (inst `(FORALL B (FORALL x
                (IMPLIES (AND (IN ,fv (FUN (PAIR ,xv ,xv) B))
                              (IN x (PAIR ,xv ,xv)))
                         (IN (,fv x) B))))
            `(A ,agv))
      (inst `(FORALL x (IMPLIES (AND (IN ,fv (FUN (PAIR ,xv ,xv) (A ,agv)))
                                     (IN x (PAIR ,xv ,xv)))
                                (IN (,fv x) (A ,agv)))) xv)
      (bc `(IMPLIES (AND (IN ,fv (FUN (PAIR ,xv ,xv) (A ,agv)))
                         (IN ,xv (PAIR ,xv ,xv)))
                    (IN (,fv ,xv) (A ,agv))))
      (di)
      (define u-fxa2 (last-node))
        (ass)
      (refocus! u-fxa2)
        (ass)
    (refocus! u-fxa)

    ;; group-left-id
    (ta 'group-left-id)
    (inst '(FORALL s (IMPLIES (IS-GROUP s)
              (FORALL a (IMPLIES (IN a (A s)) (= ((MUL s) (E s) a) a))))) agv)
    (cut `(FORALL a (IMPLIES (IN a (A ,agv)) (= ((MUL ,agv) (E ,agv) a) a))))
    (define u-gli (last-node))
      (bc `(IMPLIES (IS-GROUP ,agv)
              (FORALL a (IMPLIES (IN a (A ,agv)) (= ((MUL ,agv) (E ,agv) a) a)))))
      (ass)
    (refocus! u-gli)
    (inst `(FORALL a (IMPLIES (IN a (A ,agv)) (= ((MUL ,agv) (E ,agv) a) a)))
          `(,fv ,xv))
    (bc `(IMPLIES (IN (,fv ,xv) (A ,agv))
                  (= ((MUL ,agv) (E ,agv) (,fv ,xv)) (,fv ,xv))))
    (ass)))

;;; ---------------------------------------------------------------------
;;; ARCHIVED: finsum-type
;;; PSS entry: theorem-library/finsum-type.scm
;;; ---------------------------------------------------------------------
;;; -----------------------------------------------------------------------
;;; finsum-type:  FINSUM(ag, f, S) in A(ag)  for ag abelian, S finite,
;;; f : S -> A(ag).  mac FINSUM exposes the SUM-AG; bc* applies sum-ag-type,
;;; and its ENUM-FAM-in-FUN(NN,A ag) antecedent is discharged by bc* with
;;; enum-fam-in-fun.  Re-derived with the bc* matching-backchain tactic --
;;; was a ~100-line inst-chain proof.  Dev: prover/scratch-fs2.scm.
(prove-and-install! 'finsum-type
  (lambda ()
    (sp (make-wff
         '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
            (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
            (FORALL f (IMPLIES (IN f (FUN S (A ag)))
              (IN (FINSUM ag f S) (A ag)))))))))))
    (define Sv (eigen-name 'S (+ *fresh-counter* 1)))
    (di) (di) (di) (di) (di)
    (mac 'FINSUM)
    ;; goal: (IN (SUM-AG agv (ENUM-FAM agv fv (FIN-ENUM Sv) (CARD Sv))
    ;;                       (CARD Sv)) (A agv))
    (bc* 'sum-ag-type ()
      (ass)                                   ; IS-ABELIAN-GROUP agv
      (bc* 'enum-fam-in-fun ((S Sv))           ; ENUM-FAM family typed
        (ass)                                 ;   (CARD Sv) in NN
        (bc* 'abelian-group-is-group () (ass)) ;   IS-GROUP agv
        (bc* 'bijection-in-fun ()              ;   FIN-ENUM Sv a function
          (bc* 'fin-enum-is-bijection () (ass) (ass)))
        (ass))                                ;   fv typed
      (ass))))                                ; (CARD Sv) in NN
