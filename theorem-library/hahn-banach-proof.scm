;;; hahn-banach-proof.scm -- Hahn-Banach, the one-dimension-higher extension
;;; step (real normed vector space), MACHINE-PROVEN modulo the warranted core.
;;;
;;;   m real NVS, s a subspace, f a bounded linear functional on s, v notin s
;;;   => there is g on s' = SPAN-ADD-ONE(m,s,v) extending f, linear, with the
;;;      SAME bound  |g(w)| <= ||f||_s * ||w||.
;;;
;;; Construction: g(y + r.v) = f(y) + r.alpha for a scalar alpha chosen so the
;;; bound survives.  Two imported facts are warranted (reference):
;;;   hb-gap            -- analytic core: an alpha exists with
;;;                        |f(y)+r.alpha| <= M*||y+r.v|| (sup<=inf, RR-complete).
;;;   hb-extend-construct-- linear-algebra core: for ANY alpha,
;;;                        g(y+r.v)=f(y)+r.alpha is a well-defined linear
;;;                        functional on s' extending f (v notin s).
;;; What we PROVE is the norm-preserving payoff: g's bound by M, via hb-gap.
;;;
;;; Antecedent AND-chains are built with conjuncts->and to avoid deep manual
;;; paren nesting.  Reuses deriv-constant-proof's global dc-* helpers; no bc*.

;;; RETIRED 2026-09-17 (proven): span-add-one-membership -- theorem-library/rake-algebra.scm
;;; (the SEP-membership recipe: span-add-one-unfold, then sep-me / sep-mi).  It was
;;; an add-to-pss here, cited at the `mac-h' below, which now finds the theorem.
;;; ---- warranted core ----
;;; hb-gap PROVEN modulo 0 in theorem-library/rake-hb-gap.scm (2026-09-19)
(topic! 'hb-gap 'analysis)

;;; hb-extend-construct PROVEN modulo 0 (2026-09-19, rake batch 7) in theorem-library/rake-hb-extend-construct.scm
(topic! 'hb-extend-construct 'analysis)

;;; ---- the theorem: norm-preserving one-dimension extension ----
(sp `(FORALL m (FORALL s (FORALL f (FORALL v
     (IMPLIES ,(conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                 (IS-SUBMODULE m s)
                                 (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                                 (IN v (VEC m))
                                 (NOT (IN v s))))
       (FORSOME g_
         ,(conjuncts->and
            '((IS-LINEAR-FUNCTIONAL-ON m (SPAN-ADD-ONE m s v) g_)
              (EXTENDS-ON s g_ f)
              (FORALL w_ (IMPLIES (IN w_ (SPAN-ADD-ONE m s v))
                (<= (abs (g_ w_))
                    (* (DUAL-NORM-ON m s f) ((VNRM m) w_))))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)))   ; m,s,f,v + the typing AND
(dc-split)                                    ; split the typing AND into 5 conjuncts
(define GOAL (dc-gf))

;;; ---- (1) alpha from hb-gap ----
(define HBANT (conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                (IS-SUBMODULE m s)
                                (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                                (IN v (VEC m))
                                (NOT (IN v s)))))
(cut HBANT) (dc-grind!) (dc-focus! GOAL)        ; rebuild the antecedent AND
(quietly (lambda () (fact 'hb-gap 'm 's 'f 'v)))  ; auto-detaches -> FORSOME a_ ...
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'dual-norm-on z)))))
;; ai leaves the body (AND (IN ALPHA RR) GAPALL) as one assumption; capture
;; ALPHA from it before dc-split tears the AND apart.
(define GAPAND (dc-find (lambda (z) (and ((dc-head? 'AND) z) (dc-ment? 'dual-norm-on z)))))
(define ALPHA (cadr (cadr GAPAND)))             ; GAPAND = (AND (IN ALPHA RR) GAPALL)
(dc-split)                                       ; -> (IN ALPHA RR), GAPALL (+ re-split typing)
(define GAPALL (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'dual-norm-on z)))))

;;; ---- (2) f is linear on s (strip boundedness) ----
(cut '(IS-LINEAR-FUNCTIONAL-ON m s f))
(mac-h 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f))
(dc-split)
(quietly (lambda () (ass-all)))
(dc-focus! GOAL)

;;; ---- (3) g from hb-extend-construct (with alpha) ----
(define HEANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    '(IS-SUBMODULE m s)
                                    '(IS-LINEAR-FUNCTIONAL-ON m s f)
                                    '(IN v (VEC m))
                                    '(NOT (IN v s))
                                    (list 'IN ALPHA 'RR))))
(cut HEANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'hb-extend-construct 'm 's 'f 'v ALPHA)))  ; auto-detaches
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'extends-on z)))))
(dc-split)                                       ; linear(GW), extends-on, VALREL
(define GW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-LINEAR-FUNCTIONAL-ON) z)
                                             (dc-ment? 'span-add-one z))))))
(define VALREL (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? GW z) (dc-ment? 'vadd z)))))

;;; ---- (4) supply g = GW as the witness; the linear/extends conjuncts are
;;;          assumptions, so dc-grind! closes them and leaves only the bound. ----
(ew GW)
(dc-grind!)
(define BOUNDLEAF (car (dc-open-leaves)))
(dk-focus! BOUNDLEAF)
(di) (di)                                        ; w_ ; (IN w_ (SPAN-ADD-ONE m s v))
(define BGOAL (dc-gf))
(define W (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (dc-ment? 'span-add-one z))))))

;;; decompose w = y + r.v
(mac-h 'span-add-one-membership (list 'IN W (list 'SPAN-ADD-ONE 'm 's 'v)))
(dc-split)                                        ; (IN W (VEC m)) ; (FORSOME y_ ...)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'vadd z)))))
(dc-split)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'vadd z)))))
(dc-split)
(define EQW (dc-find (lambda (z) (and ((dc-head? '=) z) (equal? (cadr z) W) (dc-ment? 'vadd z)))))
(define YV (cadr (caddr EQW)))                    ; EQW rhs = ((VADD m) Y ((ACT m) R v))
(define RV (cadr (caddr (caddr EQW))))            ; ((ACT m) R v) -> R

;;; conditional implication-detach (no error if already detached)
;; hb-detach-opt! is in driver-kit.scm (used by three other drivers).
;;; ---- (5) the bound, by rewriting g(y+r.v) = f(y)+r.alpha and citing hb-gap ----
(subst EQW)                                       ; goal: abs(g(y+r.v)) <= M*||y+r.v||
;; VALREL: g(y+r.v) = f(y)+r.alpha
(quietly (lambda () (inst+ VALREL YV)))
(hb-detach-opt! (list 'IN YV 's))
(let ((fr (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? GW z) (dc-ment? YV z))))))
  (quietly (lambda () (inst+ fr RV))))
(hb-detach-opt! (list 'IN RV 'RR))
(define VEQ (dc-find (lambda (z) (and ((dc-head? '=) z) (dc-ment? GW z) (dc-ment? YV z) (dc-ment? RV z)))))
(subst VEQ)                                       ; goal: abs(f(y)+r.alpha) <= M*||y+r.v||
;; hb-gap (GAPALL) at y,r is exactly the goal
(quietly (lambda () (inst+ GAPALL YV)))
(hb-detach-opt! (list 'IN YV 's))
(let ((gr (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'dual-norm-on z) (dc-ment? YV z))))))
  (quietly (lambda () (inst+ gr RV))))
(hb-detach-opt! (list 'IN RV 'RR))
(quietly (lambda () (ass-all)))
(qed 'hahn-banach-extend-one)
(topic! 'hahn-banach-extend-one 'analysis)
