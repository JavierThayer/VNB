;;; scratch-sumcong.scm -- sum-ag-congruence.
;;; If g and gp agree on ORD-SEGMENT(m), then SUM-AG(ag,g,m) = SUM-AG(ag,gp,m).
;;; Prerequisite lemma for the sum-ag-splice-out STEP case (k = succ n branch).
(load "load.scm")

(define cong-goal
  '(FORALL m (IMPLIES (IN m NN)
     (FORALL ag (FORALL g (FORALL gp
       (IMPLIES (IS-ABELIAN-GROUP ag)
       (IMPLIES (IN g (FUN NN (A ag)))
       (IMPLIES (IN gp (FUN NN (A ag)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT m)) (= (g i) (gp i))))
                (= (SUM-AG ag g m) (SUM-AG ag gp m)))))))))))))

(sp (make-wff cong-goal))
(ni)

;;; ===== BASE CASE  m = 0 =====
(di)                 ; peel forall ag,g,gp
(di) (di) (di)       ; assume is-abelian-group(ag), g in fun, gp in fun
(di)                 ; assume agreement on ord-segment(0)
(mac 'sum-ag-zero)   ; both sums -> E(ag)
(rfl)
(display "--- base case closed; step case in focus ---\n") (show)

;;; ===== STEP CASE  m -> succ m =====
(define c0 *fresh-counter*)
(define mv  (eigen-name 'm  c0))
(define agv (eigen-name 'ag (+ c0 1)))
(define gv  (eigen-name 'g  (+ c0 2)))
(define gpv (eigen-name 'gp (+ c0 3)))

(di)                 ; intro m, hyp m in nn
(di)                 ; assume IH
(di)                 ; intro ag,g,gp
(di) (di) (di)       ; assume is-abelian-group, g in fun, gp in fun
(di)                 ; assume agreement on ord-segment(succ m)
(mac 'sum-ag-succ)   ; goal -> (mul)(sum g m, g m) = (mul)(sum gp m, gp m)
(display "--- step: goal exposed ---\n") (show)

;;; Formulas referenced below.
(define IH
  `(FORALL ag (FORALL g (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ag)
     (IMPLIES (IN g (FUN NN (A ag)))
     (IMPLIES (IN gp (FUN NN (A ag)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (g i) (gp i))))
              (= (SUM-AG ag g ,mv) (SUM-AG ag gp ,mv))))))))))
(define IH1
  `(FORALL g (FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,agv)
     (IMPLIES (IN g (FUN NN (A ,agv)))
     (IMPLIES (IN gp (FUN NN (A ,agv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (g i) (gp i))))
              (= (SUM-AG ,agv g ,mv) (SUM-AG ,agv gp ,mv)))))))))
(define IH2
  `(FORALL gp
     (IMPLIES (IS-ABELIAN-GROUP ,agv)
     (IMPLIES (IN ,gv (FUN NN (A ,agv)))
     (IMPLIES (IN gp (FUN NN (A ,agv)))
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (,gv i) (gp i))))
              (= (SUM-AG ,agv ,gv ,mv) (SUM-AG ,agv gp ,mv))))))))

(define A1 `(IS-ABELIAN-GROUP ,agv))
(define A2 `(IN ,gv  (FUN NN (A ,agv))))
(define A3 `(IN ,gpv (FUN NN (A ,agv))))
(define A4 `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,mv)) (= (,gv i) (,gpv i)))))
(define EQ `(= (SUM-AG ,agv ,gv ,mv) (SUM-AG ,agv ,gpv ,mv)))
(define H4 `(IMPLIES ,A4 ,EQ))
(define H3 `(IMPLIES ,A3 ,H4))
(define H2 `(IMPLIES ,A2 ,H3))
(define Hfull `(IMPLIES ,A1 ,H2))

(define Hagree `(FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ ,mv))) (= (,gv i) (,gpv i)))))
(define factA EQ)
(define factB `(= (,gv ,mv) (,gpv ,mv)))

;;; After (cut X) the prove-X child is in focus and the use-X child is the
;;; last dg node.  Auto-advance after closing prove-X is unreliable, so we
;;; capture use-X and refocus explicitly (cf. scratch-perm.scm).
(define (last-node) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (refocus! n) (set-proof-state-focus! *ps* n))

;;; --- Fact A:  SUM-AG(ag,g,m) = SUM-AG(ag,gp,m)  via the IH ---
(cut factA)
(define use-factA (last-node))
  ;; instantiate IH at ag,g,gp -> ground nested implication Hfull
  (inst IH agv) (inst IH1 gv) (inst IH2 gpv)
  ;; peel the three trivial antecedents A1,A2,A3 of Hfull
  (cut H2) (define use-H2 (last-node)) (bc Hfull) (ass) (refocus! use-H2)
  (cut H3) (define use-H3 (last-node)) (bc H2)    (ass) (refocus! use-H3)
  (cut H4) (define use-H4 (last-node)) (bc H3)    (ass) (refocus! use-H4)
  ;; goal is now factA; backchain H4 leaves the agreement antecedent A4
  (bc H4)
  (display "--- proving A4 (agreement on ord-segment m) ---\n") (show)
  (define ci *fresh-counter*)
  (define iv (eigen-name 'i ci))
  (di)                 ; intro i, assume i in ord-segment(m)  (bounded forall)
  (inst Hagree iv)
  (bc `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,mv))) (= (,gv ,iv) (,gpv ,iv))))
  (mac 'ord-segment-nn-succ)   ; -> (OR (IN i ord-seg m) (= i m))
  (oi-l)
  (ass)
(refocus! use-factA)
(display "--- Fact A closed ---\n") (show)

;;; --- Fact B:  g(m) = gp(m)  via the agreement hypothesis at i = m ---
(cut factB)
(define use-factB (last-node))
  (inst Hagree mv)
  (bc `(IMPLIES (IN ,mv (ORD-SEGMENT (succ ,mv))) (= (,gv ,mv) (,gpv ,mv))))
  (mac 'ord-segment-nn-succ)   ; -> (OR (IN m ord-seg m) (= m m))
  (oi-r)
  (rfl)
(refocus! use-factB)
(display "--- Fact B closed ---\n") (show)

;;; --- Combine: rewrite both sums and both function values ---
(subst factA)
(subst factB)
(rfl)
(display "--- FINAL ---\n") (show)
