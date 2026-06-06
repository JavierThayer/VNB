;;; scratch-perm.scm -- developing sum-ag-splice-out.
(load "load.scm")

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
