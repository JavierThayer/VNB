;;; RETIRED 2026-09-17 (proven): le-bound-mono (was an add-to-pss here) -- theorem-library/rake-analysis2.scm
;;; hahn-banach-full-proof.scm -- FULL Hahn-Banach for a finite-dimensional real
;;; normed vector space, MACHINE-PROVEN modulo a warranted plumbing core.
;;;
;;;   m finite-dim real NVS, s a subspace, f a bounded linear functional on s
;;;   => there is g on ALL of VEC(m) extending f, linear, with the SAME bound
;;;      |g(w)| <= ||f||_s * ||w||  for every w.
;;;
;;; The engine is the one-dimension step `hahn-banach-extend-one' (proven in
;;; hahn-banach-proof.scm), iterated to the whole space.  Finite-dimensionality
;;; (= noetherian, the ascending chain condition) is what makes the iteration
;;; terminate Zorn-free: among the subspaces to which f extends norm-preservingly
;;; there is a MAXIMAL one, and a maximal one must be the whole space -- else
;;; one more application of the one-step extension would enlarge it.
;;;
;;; PROVEN content (trust:none modulo the warranted core):
;;;   good-step  -- if t is a norm-preservingly-reachable subspace and x notin t,
;;;                 then SPAN-ADD-ONE(m,t,x) is reachable too (uses extend-one).
;;;   hahn-banach -- the headline: a maximal reachable subspace is everything.
;;;
;;; Warranted plumbing (reference / well-known structural facts):
;;;   hb-good-has-maximal  -- noetherian => the reachable family has a maximal elt
;;;   (dual-norm-on-nonneg / dual-norm-on-le-bound and span-add-one-{superset,has-v}
;;;    RETIRED 2026-09-19: false or underdetermined as stated; PROVEN under the
;;;    guarded `-nvs' names -- see the retirement notes below)
;;;   span-add-one-submodule  -- structure of s + RR.v
;;;   submodule-subset / subset-mem / subset-trans / proper-subset-witness  -- set plumbing
;;;   extends-on-trans / vnrm-nonneg
;;;
;;; Loads after hahn-banach-proof.scm.  Reuses deriv-constant's global dc-* helpers.

;;; ====================================================================
;;; warranted plumbing
;;; ====================================================================
;;; NPE / GOOD-SUB (the reachable-subspace vocabulary), good-sub-submodule, and
;;; hb-good-has-maximal (noetherian => a maximal reachable subspace exists) are
;;; now defined and PROVEN in noetherian-maximal-proof.scm, which loads first.

;;; RETIRED 2026-09-19 (rake batch 7): dual-norm-on-nonneg and dual-norm-on-le-bound
;;; were UNDERDETERMINED as stated (the IOTA need not denote: nothing types (VNRM m)
;;; without an NVS guard).  Counterexample and the guarded replacements
;;; dual-norm-on-nonneg-nvs / dual-norm-on-le-bound-nvs (both `modulo 0'):
;;; theorem-library/rake-dual-norm-spec.scm, sections (7) and (8); digest in
;;; scratchpad/triage/RAKE-BATCH7-REPORTS.md (7-A).  The citations below carry the
;;; added antecedents (IS-NORMED-VECTOR-SPACE m) and (SUBSET s (VEC m)).

;;; RETIRED 2026-09-19 (rake batch 7): span-add-one-superset and span-add-one-has-v
;;; were FALSE as stated (IS-SUBMODULE(m,t) says nothing about m's module laws).
;;; Counterexample and the guarded replacements span-add-one-superset-nvs /
;;; span-add-one-has-v-nvs (both `modulo 0'):
;;; theorem-library/rake-span-add-one-guarded.scm; digest in
;;; scratchpad/triage/RAKE-BATCH7-REPORTS.md (7-B).

;;; span-add-one-submodule PROVEN modulo 0 in theorem-library/rake-hb-submodules.scm (2026-09-19)
(topic! 'span-add-one-submodule 'analysis)

;; submodule-subset is NOT restated here: it is a definitional projection of
;; IS-SUBMODULE (structure-library/finite-dimensional.scm).  Until 2026-09-16 this
;; file re-added it as an asserted PSS entry with a `reference' warrant, which
;; re-installed the name and billed a definitional fact as debt in every proof
;; loaded after this point.

;;; subset-mem and subset-trans MOVED and PROVEN, 2026-07-27:
;;; theorem-library/subset-lemmas.scm, which loads long before this file.  Both
;;; were asserted here `well-known'; both are three tactic steps off subset-def.
;;; The citations at :227 and :242 below are unchanged and now resolve to the
;;; proven theorems.

;;; proper-subset-witness RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; extends-on-trans RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; vnrm-nonneg RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; typing: the norm of a vector, and |g(w)| for a functional, are reals.
;;; vnrm-real is PROVEN (2026-08-31) in theorem-library/op-typing.scm, with the
;;; other six applied-form op typings: one driver over the IS-X unfold plus
;;; apply-tupling-2 and fun-apply-type-c -- the derivation the warrant here
;;; recited.

;;; linfun-app-abs-real RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; pure-RR monotone compose: p <= a*n, a <= b, 0 <= n  =>  p <= b*n.
;;; ====================================================================
;;; PROVEN  good-step:  t reachable and x notin t  =>  t + RR.x reachable.
;;; The one-dimension extension hahn-banach-extend-one, glued to the
;;; reachability bookkeeping.
;;; ====================================================================

;;; local: focus an OPEN leaf whose goal sexp satisfies `pred'.
;; hbf-focus-open! is in driver-kit.scm (used by norm-as-sup-proof).
(sp '(FORALL m (FORALL s (FORALL f (FORALL t (FORALL x
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                (AND (GOOD-SUB m s f t)
                 (AND (IN x (VEC m)) (NOT (IN x t))))))
       (GOOD-SUB m s f (SPAN-ADD-ONE m t x)))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))   ; m,s,f,t,x + antecedent AND
(dc-split)
(define GSGOAL (dc-gf))
(define MM '(DUAL-NORM-ON m s f))

;;; unpack reachability of t: a norm-preserving extension GW
(mac-h 'GOOD-SUB '(GOOD-SUB m s f t))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'npe z)))))
(define NPEH (dc-find (dc-head? 'NPE)))
(define GW (list-ref NPEH 5))
(mac-h 'NPE NPEH)
(dc-split)                                       ; SUBMODULE t, SUBSET s t, LIN t GW, EXTENDS, BND t
(define BNDt (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? GW z) (dc-ment? 'dual-norm-on z)))))
(define LINt (dc-find (lambda (z) (and ((dc-head? 'IS-LINEAR-FUNCTIONAL-ON) z) (equal? (caddr z) 't)))))

;;; the SUBSET antecedent of the guarded dual-norm-on-* forms: SUBSET s t is
;;; NPE's second conjunct (landed above), submodule-subset gives SUBSET t (VEC m)
;;; (definitional, no bill), and subset-trans composes them.  Both inclusions are
;;; used again at :189 / :195 below.
(quietly (lambda () (fact 'submodule-subset 'm 't)))            ; SUBSET t (VEC m)
(quietly (lambda () (fact 'subset-trans 's 't '(VEC m))))       ; SUBSET s (VEC m)

;;; M = ||f||_s is a nonnegative real
(quietly (lambda () (fact 'dual-norm-on-nonneg-nvs 'm 's 'f)))
(dc-split)                                       ; (IN M RR), (<= 0 M)

;;; GW is a bounded linear functional on t (witness c = M)
(define BGW (list 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON 'm 't GW))
(cut BGW)
(mac 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON)
(quietly (lambda () (dc-grind!)))                ; closes the LINEAR conjunct, stalls at FORSOME c
(hbf-focus-open! (lambda (g) (and (pair? g) (eq? (car g) 'FORSOME))))
(ew MM)
(quietly (lambda () (dc-grind!)))                ; (IN M RR),(<=0 M),(bound=BNDt) all by ass
(dc-focus! GSGOAL)

;;; apply the proven one-step extension: get GX on SPAN-ADD-ONE(m,t,x)
(define EOANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    '(IS-SUBMODULE m t)
                                    BGW
                                    '(IN x (VEC m))
                                    '(NOT (IN x t)))))
(cut EOANT) (dc-grind!) (dc-focus! GSGOAL)       ; combined antecedent so fact auto-detaches
(quietly (lambda () (fact 'hahn-banach-extend-one 'm 't GW 'x)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'extends-on z) (dc-ment? GW z)))))
(dc-split)                                       ; LIN SPAN GX, EXTENDS t GX GW, BND SPAN GX
(define LINu (dc-find (lambda (z) (and ((dc-head? 'IS-LINEAR-FUNCTIONAL-ON) z) (dc-ment? 'span-add-one z)))))
(define GX (cadddr LINu))
(define BNDu (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? GX z) (dc-ment? 'span-add-one z)))))
(define EXTu (dc-find (lambda (z) (and ((dc-head? 'EXTENDS-ON) z) (equal? (cadr z) 't)))))
(define SPANtx (list 'SPAN-ADD-ONE 'm 't 'x))

;;; reachability plumbing for SPAN-ADD-ONE(m,t,x) (curried supports auto-detach)
(quietly (lambda () (fact 'span-add-one-submodule 'm 't 'x)))   ; IS-SUBMODULE m (SPAN)
(quietly (lambda () (fact 'span-add-one-superset-nvs 'm 't 'x)))    ; SUBSET t (SPAN)
(quietly (lambda () (fact 'subset-trans 's 't SPANtx)))         ; SUBSET s (SPAN)
(quietly (lambda () (fact 'extends-on-trans 's 't GX GW 'f)))   ; EXTENDS-ON s GX f

;;; supply GX as the witness and discharge the NPE conjuncts
(mac 'GOOD-SUB)                                  ; FORSOME g_ (NPE m s f (SPAN) g_)
(ew GX)
(mac 'NPE)                                       ; AND5
(quietly (lambda () (dc-grind!)))                ; closes submodule/subset/linear/extends; bound remains

;;; the bound leaf: |GX(w)| <= ||f||_s ||w|| on SPAN-ADD-ONE(m,t,x)
(hbf-focus-open! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL))))
(di) (di)                                        ; w_ ; (IN w_ (SPAN))
(define WW (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) SPANtx))))))
;; typing
(quietly (lambda () (fact 'submodule-subset 'm SPANtx)))        ; SUBSET (SPAN) (VEC m)
(quietly (lambda () (fact 'subset-mem-fwd SPANtx '(VEC m) WW)))     ; IN WW (VEC m)
(quietly (lambda () (fact 'vnrm-real 'm WW)))                   ; IN ||WW|| RR
(quietly (lambda () (fact 'vnrm-nonneg 'm WW)))                 ; 0 <= ||WW||
(quietly (lambda () (fact 'dual-norm-on-nonneg-nvs 'm 't GW)))  ; (IN (DUAL m t GW) RR) AND (0 <= ...)
(dc-split)                                                      ; split that AND so IN _ RR is standalone
(quietly (lambda () (fact 'linfun-app-abs-real 'm SPANtx GX WW))) ; IN |GX WW| RR
;; the two inequalities
(quietly (lambda () (inst+ BNDu WW)))
(hb-detach-opt! (list 'IN WW SPANtx))                          ; |GX WW| <= (DUAL m t GW) ||WW||
(quietly (lambda () (fact 'dual-norm-on-le-bound-nvs 'm 't GW MM))) ; (DUAL m t GW) <= ||f||_s
;; compose:  |GX WW| <= (DUAL m t GW) ||WW|| <= ||f||_s ||WW||
(quietly (lambda () (fact 'le-bound-mono
                      (list 'abs (list GX WW))
                      (list 'DUAL-NORM-ON 'm 't GW)
                      MM
                      (list (list 'VNRM 'm) WW))))
(quietly (lambda () (ass-all)))
(qed 'good-step)
(topic! 'good-step 'analysis)

;;; ====================================================================
;;; PROVEN  hahn-banach (finite-dimensional real NVS):  a bounded linear
;;; functional on a subspace extends, norm-preservingly, to the whole space.
;;; A maximal reachable subspace (hb-good-has-maximal) must be everything,
;;; else good-step would enlarge it.
;;; ====================================================================
(sp `(FORALL m (FORALL s (FORALL f
     (IMPLIES ,(conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                 (IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE m))
                                 (IS-SUBMODULE m s)
                                 (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)))
       (FORSOME g_ (AND (IS-LINEAR-FUNCTIONAL-ON m (VEC m) g_)
                   (AND (EXTENDS-ON s g_ f)
                        (FORALL w_ (IMPLIES (IN w_ (VEC m))
                          (<= (abs (g_ w_)) (* (DUAL-NORM-ON m s f) ((VNRM m) w_)))))))))))))
(quietly (lambda () (di)(di)(di)(di)))            ; m,s,f + antecedent AND
(dc-split)                                        ; NVS, FINDIM, SUBMODULE s, BOUNDED s f
(define HBGOAL (dc-gf))

;;; a maximal reachable subspace T
(quietly (lambda () (fact 'hb-good-has-maximal 'm 's 'f)))   ; curried -> FORSOME t (...)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'good-sub z)))))
(dc-split)                                        ; GOOD-SUB(T), MAX
(define GSUBT (dc-find (lambda (z) (and ((dc-head? 'GOOD-SUB) z)))))
(define HB-TT (list-ref GSUBT 4))                    ; GOOD-SUB m s f T
(define MAXT (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (dc-ment? 'good-sub z)))))

;;; T is a submodule (without destroying GOOD-SUB(T), which good-step needs)
(quietly (lambda () (fact 'good-sub-submodule 'm 's 'f HB-TT)))   ; IS-SUBMODULE m T

;;; ---- claim: T = VEC(m) ----
(cut (list '= HB-TT '(VEC m)))                       ; auto-focus this subgoal
(pbc)                                             ; assume NOT (= T (VEC m)); goal FALSITY
(quietly (lambda () (fact 'submodule-subset 'm HB-TT)))          ; SUBSET T (VEC m)
(quietly (lambda () (fact 'proper-subset-witness HB-TT '(VEC m))))  ; needs SUBSET, NOT(= T VECm)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'vec z) (dc-ment? HB-TT z)))))
(dc-split)                                        ; (IN XW (VEC m)), (NOT (IN XW T))
(define XW (cadr (dc-find (lambda (z) (and ((dc-head? 'IN) z) (equal? (caddr z) '(VEC m))
                                           (not (equal? (cadr z) '(VZERO m))))))))
(define UU (list 'SPAN-ADD-ONE 'm HB-TT XW))

;;; good-step: U = T + RR.XW is reachable
(define GSANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                                    (list 'GOOD-SUB 'm 's 'f HB-TT)
                                    (list 'IN XW '(VEC m))
                                    (list 'NOT (list 'IN XW HB-TT)))))
(cut GSANT) (dc-grind!) (dc-focus-case! (list 'NOT (list 'IN XW HB-TT)))
(quietly (lambda () (fact 'good-step 'm 's 'f HB-TT XW)))         ; GOOD-SUB(U)
(quietly (lambda () (fact 'span-add-one-superset-nvs 'm HB-TT XW)))   ; SUBSET T U

;;; maximality forces T = U, but XW in U and XW notin T -- contradiction
(quietly (lambda () (fact 'span-add-one-has-v-nvs 'm HB-TT XW)))   ; IN XW U
(quietly (lambda () (inst+ MAXT UU)))                       ; IMPLIES (AND GOOD-SUB(U) SUBSET T U)(= T U)
(define ANDMU (list 'AND (list 'GOOD-SUB 'm 's 'f UU) (list 'SUBSET HB-TT UU)))
(cut ANDMU) (dc-grind!) (dc-focus-case! (list 'NOT (list 'IN XW HB-TT)))
(dc-detach-impl! ANDMU)                                     ; (= T U)
(cut (list 'IN XW HB-TT))                                      ; auto-focus
(subst (list '= HB-TT UU))                                     ; (IN XW T) -> (IN XW U)
(quietly (lambda () (ass-all)))
(dc-focus-case! (list 'NOT (list 'IN XW HB-TT)))
(ai (dc-find (lambda (z) (and ((dc-head? 'NOT) z) (dc-ment? XW z) (dc-ment? HB-TT z)))))  ; not-elim closes falsity

;;; ---- T = VEC(m); transport GT's facts and finish ----
(dc-focus! HBGOAL)
(define EQT (list '= HB-TT '(VEC m)))
(mac-h 'GOOD-SUB (list 'GOOD-SUB 'm 's 'f HB-TT))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'npe z)))))
(define NPEHt (dc-find (dc-head? 'NPE)))
(define GT (list-ref NPEHt 5))
(mac-h 'NPE NPEHt)
(dc-split)                                       ; SUBMODULE T, SUBSET s T, LIN m T GT, EXT s GT f, BND T

;;; supply g = GT; rewrite VEC(m) back to T (since T = VEC(m)) and discharge
(define POSTEW #f)
(ew GT)
(set! POSTEW (dc-gf))
(define FLIP (list '= '(VEC m) HB-TT))
(cut FLIP)                                        ; (= (VEC m) T)
(subst EQT)                                       ; EQT=(= T (VEC m)); T->(VEC m): (= (VEC m)(VEC m))
;; vec-is-set is a THEOREM since 2026-09-17 (theorem-library/rake-setoid.scm); its add-to-pss here was retired
(quietly (lambda () (fact 'vec-is-set 'm)))       ; (IN (VEC m) SET) definedness for rfl
(rfl)
(dc-focus! POSTEW)
(subst FLIP)                                      ; rewrite (VEC m) -> T in the goal
(quietly (lambda () (dc-grind!)))                 ; linear/extends/bound all match the T-facts
(qed 'hahn-banach)
(topic! 'hahn-banach 'analysis)
