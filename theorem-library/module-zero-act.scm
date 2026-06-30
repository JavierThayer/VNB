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

(let* ((goal (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
       (lhs  (binary-left goal))         ; ((act S) (zero (scal S)) X) -- = is binary
       (S    (arg (opr lhs)))            ; opr lhs = (act S); its argument is S
       (PTS    (arg-ref lhs 2))            ; 2nd argument of the action application
       ;; subterms in SURFACE syntax, eigenvars spliced into positional ~a holes:
       (SR    (tm "scal(~a)" S))               ; the scalar ring
       (Z     (tm "zero(~a)" SR))              ; its zero
       (AA    (tm "act(~a)(~a,~a)" S Z PTS))     ; a := 0.x
       (ADD00 (tm "add(~a)(~a,~a)" SR Z Z)))   ; 0 +_R 0
  ;; --- forward facts: closures + the two equations ---
  (fact 'module-scalar-ring S)                        ; IS-RING(scal S)
  (fact 'module-scalar-zero-in S)                     ; 0 in A(scal S)
  (fact 'module-act-type S Z PTS)                       ; a in VEC(S)
  (fact 'module-act-distrib-scalar S Z Z PTS)           ; a = 0.x ; (0+0).x = a +_V a
  (fact 'ring-add-left-id SR Z)                        ; 0 +_R 0 = 0
  ;; --- key equation a +_V a = a, by rewriting with the two facts ---
  (cut   (tm "vadd(~a)(~a,~a) = ~a" S AA AA AA))
  (subst (tm "vadd(~a)(~a,~a) = act(~a)(~a,~a)" S AA AA S ADD00 PTS))
  (subst (tm "~a = ~a" ADD00 Z))
  (rfl)
  ;; --- idempotent under +_V  =>  a = 0_V ---
  (fact 'abelian-group-idempotent-is-id-module-vector-ag S AA)
  (ass))

(qed 'module-zero-act)
