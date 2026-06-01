;;; scratch-finsum.scm -- development of finsum-well-defined (complete)

(define (last-node) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (refocus! n) (set-proof-state-focus! *ps* n))
(define (S v t f) (subst-free v t f))
(define (probe tag)
  (display ";; --- ") (display tag) (display " ---") (newline)
  (display "GOAL: ")
  (display (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
  (newline)
  (display "OPEN: ")
  (display (length (dg-ungrounded-nodes (proof-state-dg *ps*))))
  (newline))

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
(probe "after mac FINSUM")

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

;;; -----------------------------------------------------------------------
;;; enum-fam-in-fun instantiation chain (P3 = G, P4 = H).
;;; EF alternates FORALL/IMPLIES except for the consecutive FORALL S / FORALL
;;; phi pair, so S is instantiated with no cut before phi.
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
;; phi := FIN-ENUM(S)  (for G / P3)
(define EFphi  (S 'phi feS (caddr EFS)))
(define EX3    (caddr EFphi))
(define EFf    (S 'f fv (caddr EX3)))
;; phi := enm  (for H / P4)
(define EFphiB (S 'phi enmv (caddr EFS)))
(define EX3B   (caddr EFphiB))
(define EFfB   (S 'f fv (caddr EX3B)))

;;; bijection-compose instantiation chain (P5).
(define BJC '(FORALL X (FORALL Y (FORALL Z (FORALL phi (FORALL psi
   (IMPLIES (AND (IN phi (BIJECTION X Y))
                 (IN psi (BIJECTION Y Z)))
            (IN (VNB-LAMBDA x (psi (phi x)))
                (BIJECTION X Z)))))))))
(define BJC1 (S 'X osn (caddr BJC)))
(define BJC2 (S 'Y Sv  (caddr BJC1)))
(define BJC3 (S 'Z osn (caddr BJC2)))
(define BJC4 (S 'phi enmv (caddr BJC3)))
(define BJC5 (S 'psi invfe (caddr BJC4)))

;;; -----------------------------------------------------------------------
;;; reusable sub-proof helpers (operate on the current focus)

;; goal:  (IN feS (BIJECTION osn Sv))  -- FIN-ENUM(S) is a bijection
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

;; goal:  (IS-GROUP agv)  -- from IS-ABELIAN-GROUP
(define (isg-inline)
  (ta 'abelian-group-is-group)
  (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) agv)
  (bc `(IMPLIES (IS-ABELIAN-GROUP ,agv) (IS-GROUP ,agv)))
  (ass))

;; goal:  (IN pt (FUN osn Sv))  -- reduces it to (IN pt (BIJECTION osn Sv))
(define (bij-in-fun-inline pt)
  (ta 'bijection-in-fun)
  (inst '(FORALL X (FORALL Y (FORALL phi
            (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))) osn)
  (inst `(FORALL Y (FORALL phi
            (IMPLIES (IN phi (BIJECTION ,osn Y)) (IN phi (FUN ,osn Y))))) Sv)
  (inst `(FORALL phi
            (IMPLIES (IN phi (BIJECTION ,osn ,Sv)) (IN phi (FUN ,osn ,Sv)))) pt)
  (bc `(IMPLIES (IN ,pt (BIJECTION ,osn ,Sv)) (IN ,pt (FUN ,osn ,Sv)))))

;;; =======================================================================
;;; main proof: apply sum-ag-permutation-invariance, then close P3-P6.
;;; =======================================================================
(ta 'sum-ag-permutation-invariance)
(inst PI n)
(cut X1) (define uX1 (last-node)) (bc PIn) (ass) (refocus! uX1)
(inst X1 agv)
(cut X2) (define uX2 (last-node)) (bc PIag) (ass) (refocus! uX2)
(inst X2 G)
(cut X3) (define uX3 (last-node)) (bc PIg)

;;; ---- P3:  G = ENUM-FAM(ag,f,FIN-ENUM(S),CARD S) in FUN(NN, A(ag)) ----
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
(probe "P3 closed")

(refocus! uX3)
(inst X3 H)
(cut X4) (define uX4 (last-node)) (bc PIh)

;;; ---- P4:  H = ENUM-FAM(ag,f,enm,CARD S) in FUN(NN, A(ag)) ----
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
(probe "P4 closed")

(refocus! uX4)
(inst X4 psi)
(cut X5) (define uX5 (last-node)) (bc PIphi)

;;; ---- P5:  psi = INVERSE-BIJ(FIN-ENUM(S)) o enm  is a bijection ----
;;; Proved with the lambda bound by x (matching bijection-compose); the
;;; cut then closes the i-bound goal by alpha-equivalence.
(cut `(IN (VNB-LAMBDA x (,invfe (,enmv x))) (BIJECTION ,osn ,osn)))
(define uP5 (last-node))
  (ta 'bijection-compose)
  (inst BJC osn) (inst BJC1 Sv) (inst BJC2 osn) (inst BJC3 enmv) (inst BJC4 invfe)
  (bc BJC5)
  (di)
  (define p5and2 (last-node))
    (ass)                     ; enm in BIJECTION(osn, Sv) -- hypothesis
  (refocus! p5and2)
    ;; invfe in BIJECTION(Sv, osn)
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
(probe "P5 closed")

(refocus! uX5)
(bc X5)

;;; ---- P6:  agreement  H(i) = G(psi(i))  for i in ORD-SEGMENT(CARD S) ----
;; FACT-feS:  FIN-ENUM(S) in BIJECTION(osn, Sv) -- shared by the steps below.
(cut `(IN ,feS (BIJECTION ,osn ,Sv)))
(define u6feS (last-node))
  (feb-inline)
(refocus! u6feS)

(define p6c *fresh-counter*)
(define iv (eigen-name 'i p6c))
(di)                           ; peel FORALL i
(di)                           ; assume (IN iv osn)

;; FACT-eiv:  enm(iv) in Sv
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

;; FACT-ivfun:  invfe in FUN(Sv, osn)
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
(probe "P6 after mac+beta")

;; LHS:  IF (IN iv osn) (f (enm iv)) (E ag)  -- condition holds
(if-true `(IF (IN ,iv ,osn) (,fv (,enmv ,iv)) (E ,agv)))
(define u6lt (last-node))
  (ass)
(refocus! u6lt)
(subst `(= (IF (IN ,iv ,osn) (,fv (,enmv ,iv)) (E ,agv)) (,fv (,enmv ,iv))))

;; RHS:  IF (IN (invfe (enm iv)) osn) (f (feS (invfe (enm iv)))) (E ag)
(if-true `(IF (IN (,invfe (,enmv ,iv)) ,osn)
              (,fv (,feS (,invfe (,enmv ,iv)))) (E ,agv)))
(define u6rt (last-node))
  ;; prove the condition  (IN (invfe (enm iv)) osn)
  (ta 'fun-apply-type)
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

;; goal now:  (= (f (enm iv)) (f (feS (invfe (enm iv)))))
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
(rfl)

(probe "FINAL")
(newline)
(display (if (proof-done? *ps*)
             ";; *** finsum-well-defined: PROOF COMPLETE ***"
             ";; !!! finsum-well-defined: STILL OPEN"))
(newline)
