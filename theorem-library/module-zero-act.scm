;;; module-zero-act.scm -- 0 . x = 0_V : the ring zero annihilates every vector.
;;;
;;; The first PROVEN theorem about MODULE, and a worked test of the forward-
;;; assembly tactic `fact' together with the MODULE-VECTOR-AG view's specialized
;;; abelian-group idempotent lemma.
;;;
;;; Maths (4 lines):  0.x = (0 +_R 0).x          [0+0=0 in the scalar ring]
;;;                       = 0.x +_V 0.x           [action distributes / ring add]
;;;   so 0.x is idempotent under +_V, hence 0.x = 0_V  [group cancellation,
;;;   i.e. the idempotent-is-identity lemma specialized to the vector group].
;;;
;;; Each step is one `fact' (forward modus-ponens application of a citable
;;; theorem): no peeling of the IS-MODULE definition, no bc* goal explosion.
;;; Eigenvariables are recovered from the goal after di, never hardcoded, so
;;; the script is immune to fresh-variable drift across loads.
;;;
;;; Loads after interactive + the module bricks + views (needs fact/cut/qed and
;;; the MODULE-VECTOR-AG specialization).

(sp (make-wff
     '(FORALL s (IMPLIES (IS-MODULE s)
        (FORALL x (IMPLIES (IN x (VEC s))
          (= ((ACT s) (ZERO (SCAL s)) x) (VZERO s))))))))
(di) (di) (di)                          ; intro s, IS-MODULE(s), x (restricted)

(let* ((goal  (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
       (lhs   (cadr goal))               ; ((act S) (zero (scal S)) X)
       (S     (cadr (car lhs)))          ; (act S) -> S
       (X     (caddr lhs))
       (Z     (list 'ZERO (list 'SCAL S)))            ; the scalar zero
       (AA    (list (list 'ACT S) Z X))               ; a := 0.x
       (ADD00 (list (list 'ADD (list 'SCAL S)) Z Z))) ; 0 +_R 0
  ;; --- forward facts: closures + the two equations ---
  (fact 'module-scalar-ring S)                        ; IS-RING(scal S)
  (fact 'module-scalar-zero-in S)                     ; 0 in A(scal S)
  (fact 'module-act-type S Z X)                       ; a in VEC(S)
  (fact 'module-act-distrib-scalar S Z Z X)           ; a = 0.x ; (0+0).x = a +_V a
  (fact 'ring-add-left-id (list 'SCAL S) Z)           ; 0 +_R 0 = 0
  ;; --- key equation a +_V a = a, by rewriting with the two facts ---
  (cut (list '= (list (list 'VADD S) AA AA) AA))
  (subst (list '= (list (list 'VADD S) AA AA) (list (list 'ACT S) ADD00 X)))
  (subst (list '= ADD00 Z))
  (rfl)
  ;; --- idempotent under +_V  =>  a = 0_V ---
  (fact 'abelian-group-idempotent-is-id-module-vector-ag S AA)
  (ass))

(qed 'module-zero-act)
