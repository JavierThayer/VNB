;;; rake-gof-deriv.scm -- rake batch 7-E: a bounded linear functional commutes
;;; with the vector Caratheodory derivative, and the Taylor-side leaves of
;;; theorem-library/vector-taylor-proof.scm that follow from it:
;;;   gof-taylor-diff (:627-632)  PROVEN here, guarded, as gof-taylor-diff-dfun
;;;   g-of-remainder  (:641-647)  PROVEN here, guarded, as g-of-remainder-dfun
;;;   gof-nth-deriv   (:656-662)  PROVEN here, guarded, as gof-nth-deriv-dfun
;;;
;;; ALL THREE LEAVES ARE UNDERDETERMINED AS STATED.  Each is a strict `=' (or a
;;; predicate whose unfold demands a FUN typing) at terms built from DERIV-V,
;;; an IOTA that need not denote, with NO differentiability hypothesis: for
;;; f(t) = |t| . v, a = 0, n = 0 and g /= 0 both sides of gof-nth-deriv are
;;; undefined, and a strict `=' between two undefined terms is FALSE.  It is
;;; the defect vtaylor-poly-in-vec and vtaylor-remainder-in-vec were repaired
;;; for on 2026-09-17, and the repair here is the same: DFUN-V(m,f,n) (plus,
;;; for the pointwise leaf, the IS-DIFF-AT-V that TAYLOR-DIFFERENTIABLE-V
;;; already carries at the interior point).  Every added antecedent is in the
;;; citer's context at vector-taylor-proof.scm:723/750/751 -- DFUN-V(m,f,n) is
;;; landed there at :707 by `taylor-v-derivs-in-fun'.
;;;
;;; WHAT THE ARC NEEDED, and what the note at vector-taylor-proof.scm:367-449
;;; said was missing:
;;;   (G1) "nothing in the tree carries a bounded linear functional through the
;;;        Caratheodory derivative" -- section (6), r8e-blf-diff-commute, with
;;;        its three bricks: (-1).u = -u (2), g(u-v) = g(u)-g(v) (3), and the
;;;        eps/delta continuity of g (6a).  A general three-space
;;;        `compose-continuous-at' is NOT needed and is still absent.
;;;   (G2) "no rule from the definedness of an IOTA to its property" -- STALE:
;;;        `iota-e' (pi-iota-in-elim!) was added 2026-09-15, one day after that
;;;        note was written.  Section (7) is the two-line bridge it makes
;;;        possible, and section (8) the induction (g o f)^(k) = g o f^(k).
;;;
;;; WINDOW.  EMPTY: this file cites NVS-METRIC-SPACE, IS-DIFF-AT-V, DERIV-V,
;;; NTH-DERIV-V and four theorems of vector-taylor-proof.scm (gof-in-fun,
;;; dfun-v-mono, diff-v-value-in-vec, rkt-nvs-vneg-in-vec), all at load
;;; position 486, and is cited from the same file at line 723.  It is a SPLICE
;;; into vector-taylor-proof.scm between line 613 (the end of the 2026-09-17
;;; block) and line 615 (`warranted cores').
;;;
;;; Helper prefix: `r8e-'.

;;; ---- file-local driver helpers ---------------------------------------

(define (r8e-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space '(IS-NORMED-VECTOR-SPACE m))
  (dk-split-all!))

(define (r8e-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-gof-deriv: proof did not close" name (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;;; `ineq' by FORMULA (rake-hb-leaves.scm's rhb-ineq!): the oracle's indices are
;;; 1-based into the context, which no driver can count after a few `fact's.
(define (r8e-ineq! . r8e-forms)
  (let ((r8e-as (dk-asms)))
    (apply ineq
           (map (lambda (f)
                  (let loop ((l r8e-as) (i 1))
                    (cond ((null? l) (error "r8e-ineq!: not in context" f))
                          ((equal? (car l) f) i)
                          (#t (loop (cdr l) (+ i 1))))))
                r8e-forms))))

;;; unfold IS-BOUNDED-LINEAR-FUNCTIONAL m g down to atoms (destructive)
(define (r8e-blf-split! . r8e-opt)
  (let ((r8e-m (if (pair? r8e-opt) (car r8e-opt) 'm))
        (r8e-g (if (pair? r8e-opt) (cadr r8e-opt) 'g)))
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'IS-BOUNDED-LINEAR-FUNCTIONAL
                                  (list 'IS-BOUNDED-LINEAR-FUNCTIONAL r8e-m r8e-g)))))
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'IS-LINEAR-FUNCTIONAL
                                  (list 'IS-LINEAR-FUNCTIONAL r8e-m r8e-g)))))))

;;; DFUN-V(m,f,n): f^(j) is a TOTAL map RR -> VEC(m) for every j <= n.  The
;;; guard vector-taylor-proof.scm's own spliced theorems carry (rkt-dfun-v
;;; there); repeated here because that helper is file-local.
(define (r8e-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "r8e-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "r8e-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

(define (r8e-dfun-v m f n)
  (list 'FORALL 'j_ (list 'IMPLIES (list 'AND '(IN j_ NN) (list '<= 'j_ n))
                          (list 'IN (list 'NTH-DERIV-V m f 'j_) (list 'FUN 'RR (list 'VEC m))))))

;;; the two laws of IS-LINEAR-FUNCTIONAL, named by what their consequent
;;; MENTIONS.  The IS-DIFF-AT-V factor identity is a FORALL mentioning BOTH
;;; VADD and ACT, so each test excludes the other operation.
(define (r8e-additivity)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'VADD) (not (dk-contains? f 'ACT))))
           "the additivity law of g"))
(define (r8e-homogeneity)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'ACT) (not (dk-contains? f 'VADD))))
           "the homogeneity law of g"))

(define r8e-lin-hom
  '(FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= (g ((ACT m) r_ x_)) (* r_ (g x_))))))))
(define r8e-lin-add
  '(FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= (g ((VADD m) x_ y_)) (+ (g x_) (g y_))))))))
(define r8e-bnd
  '(FORSOME c_ (AND (IN c_ RR)
               (AND (<= 0 c_)
                    (FORALL x_ (IMPLIES (IN x_ (VEC m))
                      (<= (abs (g x_)) (* c_ ((VNRM m) x_)))))))))

;;; the fully detached beta law of COMPOSE for the inner map F: the FORALL that
;;; mentions COMPOSE and F and no longer carries a FUN typing.
(define (r8e-capply f)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'COMPOSE)
                             (dk-contains? fm f)
                             (not (dk-contains? fm 'FUN))))
           "the COMPOSE beta law"))

;;; =====================================================================
;;; (1) TWO PROJECTIONS OF THE IS-NORMED-VECTOR-SPACE UNFOLD.
;;; theorem-library/nvs-act-laws.scm projects the RIGHT identity law
;;; (nvs-vzero-right); the LEFT one and the inverse law are needed here.
;;; =====================================================================

;; vzero + u = u
(r8e-open!
 '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
    (FORALL u_ (IMPLIES (IN u_ (VEC m))
      (= ((VADD m) (VZERO m) u_) u_))))))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'is-identity '(IS-IDENTITY (VADD m) (VZERO m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8e-check! 'r8e-vzero-left)

;; (-u) + u = vzero
(r8e-open!
 '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
    (FORALL u_ (IMPLIES (IN u_ (VEC m))
      (= ((VADD m) ((VNEG m) u_) u_) (VZERO m)))))))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'has-inverses
                               '(HAS-INVERSES (VADD m) (VZERO m) (VNEG m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8e-check! 'r8e-vneg-inv)

;;; =====================================================================
;;; (2) (-1) . u = -u.   The module fact the Hahn-Banach triage records as
;;; missing ("no NVS/module lemma states ACT(-1,v) = VNEG(v)").  From the
;;; three action laws of nvs-act-laws.scm at the base point y := -u:
;;;   (-u + 1.u) + (-1).u = -u + (1 + -1).u = -u + 0.u = -u
;;; and the left side is (-u + u) + (-1).u = vzero + (-1).u = (-1).u.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
          (= ((ACT m) (- 0 1) u_) ((VNEG m) u_))))))))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 1)
(fact 'rkt-nvs-vneg-in-vec 'm 'u_)
(fact 'nvs-act-in-vec 'm '(- 0 1) 'u_)
(fact 'r8e-vzero-left 'm '((ACT m) (- 0 1) u_))
(subst '(= ((ACT m) (- 0 1) u_) ((VADD m) (VZERO m) ((ACT m) (- 0 1) u_))))
(fact 'r8e-vneg-inv 'm 'u_)
(subst '(= (VZERO m) ((VADD m) ((VNEG m) u_) u_)))
(fact 'nvs-act-one 'm 'u_ '((VNEG m) u_))
(subst '(= ((VADD m) ((VNEG m) u_) u_) ((VADD m) ((VNEG m) u_) ((ACT m) 1 u_))))
(fact 'nvs-act-collect 'm 1 '(- 0 1) 'u_ '((VNEG m) u_))
(subst '(= ((VADD m) ((VADD m) ((VNEG m) u_) ((ACT m) 1 u_)) ((ACT m) (- 0 1) u_))
           ((VADD m) ((VNEG m) u_) ((ACT m) (+ 1 (- 0 1)) u_))))
(have! '(= (+ 1 (- 0 1)) 0) (lambda () (arith)))
(subst '(= (+ 1 (- 0 1)) 0))
(fact 'nvs-act-zero 'm 'u_ '((VNEG m) u_))
(ass)
(r8e-check! 'r8e-act-neg-one)

;;; =====================================================================
;;; (3) g(-u) = -g(u)  and  g(u + (-v)) = g(u) - g(v), for a bounded linear g.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
          (= (g ((VNEG m) u_)) (- 0 (g u_)))))))))))
(dk-peel!)
(fact 'r8e-act-neg-one 'm 'u_)
(r8e-blf-split!)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'u_)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 1)
(subst '(= ((VNEG m) u_) ((ACT m) (- 0 1) u_)))
(subst (dk-apply! (r8e-homogeneity) '(- 0 1) 'u_))
(crs)
(r8e-check! 'r8e-blf-vneg)

(sp (make-wff
     '(FORALL m (FORALL g (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
        (FORALL v_ (IMPLIES (IN v_ (VEC m))
          (= (g ((VADD m) u_ ((VNEG m) v_))) (- (g u_) (g v_)))))))))))))
(dk-peel!)
(fact 'r8e-blf-vneg 'm 'g 'v_)
(fact 'rkt-nvs-vneg-in-vec 'm 'v_)
(r8e-blf-split!)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'u_)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'v_)
(subst (dk-apply! (r8e-additivity) 'u_ '((VNEG m) v_)))
(subst '(= (g ((VNEG m) v_)) (- 0 (g v_))))
(crs)
(r8e-check! 'r8e-blf-sub)

;;; =====================================================================
;;; (4) the distance of NVS-METRIC-SPACE, read off.  NVS-METRIC-SPACE is a
;;; def-functoid LIST, so `slot' has no projection for it: unfold, slot,
;;; nth-r -- nvs-ms-pts' recipe (vector-taylor-proof.scm:196) one storey
;;; down -- then beta at the pair.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
        (FORALL v_ (IMPLIES (IN v_ (VEC m))
          (== ((DIST (NVS-METRIC-SPACE m)) u_ v_)
              ((VNRM m) ((VADD m) u_ ((VNEG m) v_))))))))))))
(dk-peel!)
(fact 'pair-in-cartesian '(VEC m) '(VEC m) 'u_ 'v_)
(mac 'NVS-METRIC-SPACE)
(slot 'DIST)
(nth-r)
(lam-b)
(qrfl)
(r8e-check! 'r8e-nvs-dist)

;;; =====================================================================
;;; (5) THE EPSILON/(c+1) STEP, as a lemma: for c >= 0 and eps > 0 there is a
;;; positive d with c*z <= eps for every z <= d.  This is the arithmetic every
;;; "a bounded linear map is continuous" proof needs, and the tree has it
;;; nowhere (rr-pos-halvable is the c = 2 case of the same shape).
;;; =====================================================================
(define r8e-K '(+ 1 c_))
(define r8e-R '(recip (+ 1 c_)))
(define r8e-D '(* e_ (recip (+ 1 c_))))

(sp (make-wff
     '(FORALL c_ (IMPLIES (IN c_ RR) (IMPLIES (<= 0 c_)
        (FORALL e_ (IMPLIES (POS-RR e_)
          (FORSOME d_ (AND (POS-RR d_)
            (FORALL z_ (IMPLIES (IN z_ RR) (IMPLIES (<= z_ d_)
              (<= (* c_ z_) e_)))))))))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'e_)
(fact 'rr-lt-of-pos-rr 'e_)
(fact 'rr-one-in)
(have! (list 'AND '(IN 1 RR) '(IN c_ RR)))
(fact 'rr-add-closed 1 'c_)
(fact 'rr-one-plus-nonneg-pos 'c_)
(fact 'rr-pos-ne-zero r8e-K)
(have! (list 'AND (list 'IN r8e-K 'RR) (list 'NOT (list '= r8e-K 0))))
(fact 'rr-recip-closed r8e-K)
(fact 'rr-recip-inverse r8e-K)
(fact 'rr-recip-pos r8e-K)
(have! (list 'AND '(IN e_ RR) (list 'IN r8e-R 'RR)))
(fact 'rr-mul-closed 'e_ r8e-R)
(fact 'rr-mul-pos 'e_ r8e-R)
(mac-h '< (list '< 0 r8e-D))
(dk-split! (list 'AND (list '<= 0 r8e-D) (list 'NOT (list '= 0 r8e-D))))
(have! (list '<= 'c_ r8e-K) (lambda () (r8e-ineq! '(IN c_ RR))))
;; (1+c).(e.recip(1+c)) = e -- a ring identity in e and the opaque recip, then
;; the reciprocal law.
(have! (list '= (list '* r8e-K r8e-D) 'e_)
       (lambda ()
         (have! (list '= (list '* r8e-K r8e-D) (list '* 'e_ (list '* r8e-K r8e-R)))
                (lambda () (crs)))
         (subst (list '= (list '* r8e-K r8e-D) (list '* 'e_ (list '* r8e-K r8e-R))))
         (subst (list '= (list '* r8e-K r8e-R) 1))
         (crs)))
(ew r8e-D)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'POS-RR)
       (begin (mac 'pos-rr) (from-context!))
       (begin
         ;; dk-peel!, not di: the guarded binder and the `z <= d' antecedent are
         ;; two di's, and the eigenvariable is read off the GOAL (* c_ z_) <= e_
         (dk-peel!)
         (let ((r8e-z (caddr (cadr (dk-goal)))))
           (have! (list 'AND (list 'IN r8e-z 'RR) '(IN c_ RR)))
           (fact 'rr-mul-closed r8e-z 'c_)
           (have! (list 'AND (list 'IN r8e-D 'RR) '(IN c_ RR)))
           (fact 'rr-mul-closed r8e-D 'c_)
           (have! (list 'AND '(IN c_ RR) (list 'IN r8e-D 'RR)))
           (fact 'rr-mul-closed 'c_ r8e-D)
           (have! (list 'AND (list 'IN r8e-K 'RR) (list 'IN r8e-D 'RR)))
           (fact 'rr-mul-closed r8e-K r8e-D)
           ;; c.z = z.c, so the monotone step can put the multiplier on the right
           (have! (list '= (list '* 'c_ r8e-z) (list '* r8e-z 'c_)) (lambda () (crs)))
           (subst (list '= (list '* 'c_ r8e-z) (list '* r8e-z 'c_)))
           (fact 'rr-mul-le-right r8e-z r8e-D 'c_)
           (have! (list '<= (list '* r8e-D 'c_) 'e_)
                  (lambda ()
                    (have! (list '= (list '* r8e-D 'c_) (list '* 'c_ r8e-D))
                           (lambda () (crs)))
                    (subst (list '= (list '* r8e-D 'c_) (list '* 'c_ r8e-D)))
                    (fact 'rr-mul-le-right 'c_ r8e-K r8e-D)
                    (have! (list '<= (list '* r8e-K r8e-D) 'e_)
                           (lambda ()
                             (subst (list '= (list '* r8e-K r8e-D) 'e_))
                             (fact 'rr-leq-reflexive 'e_)
                             (ass)))
                    (fact 'rr-le-trans-c (list '* 'c_ r8e-D) (list '* r8e-K r8e-D) 'e_)
                    (ass)))
           (fact 'rr-le-trans-c (list '* r8e-z 'c_) (list '* r8e-D 'c_) 'e_)
           (ass))))))
(r8e-check! 'r8e-eps-over)

;;; =====================================================================
;;; (6a) A BOUNDED LINEAR FUNCTIONAL CARRIES CONTINUITY INTO THE REALS:
;;;      h continuous at t into the NORM metric  =>  g o h continuous at t.
;;; The one analytic step of the arc.  Given eps, r8e-eps-over turns the bound
;;; c into a tolerance d on the norm, h's own continuity supplies a delta for
;;; d, and |g(h t) - g(h b)| = |g(h t - h b)| <= c*||h t - h b|| =
;;; c*dist(h t, h b) <= eps.  The tree's `compose-continuous-at' is stated at
;;; RR-MS/RR-MS only, so no composition theorem applies here.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (FORALL h (FORALL t
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (IMPLIES (IN h (FUN RR (VEC m)))
        (IMPLIES (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) h t)
          (IS-CONTINUOUS-AT RR-MS RR-MS (COMPOSE g h) t)))))))))))
(dk-peel!)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-bnd                   (lambda () (r8e-blf-split!) (ass)))
(have! '(== RR (PTS RR-MS)) (lambda () (slot 'PTS) (qrfl)))
(let* ((r8e-hv 'h)
       (r8e-gh '(COMPOSE g h))
       (r8e-cv (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                     (dk-contains? f 'VNRM)))
                                    "the boundedness existential")))
       (r8e-bound (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VNRM)
                                                       (dk-contains? f 'abs)))
                                      "the bound universal"))))
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'is-continuous-at
                                '(IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) h t)))))
  (fact 'rr-is-set)
  (fact 'gof-in-fun 'm 'h 'g)
  (have! '(IN t RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
  (fact 'fun-apply-type-c 'h 'RR '(VEC m) 't)
  (have! (list 'AND (list 'IN 'h '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'h)
     (mac 'is-continuous-at)
     (dk-conj-close!
      (lambda ()
        (let ((r8e-g3 (dk-goal)))
          (cond
           ((eq? (car r8e-g3) 'IS-METRIC-SPACE) (ass))
           ((eq? (car r8e-g3) 'IN) (subst '(== (PTS RR-MS) RR)) (ass))
           (#t                                   ; the eps universal
            (dk-peel!)
            (let* ((r8e-eps (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)))
                                           "the eps typing")))
                   (r8e-dd (begin
                             (fact 'r8e-eps-over r8e-cv r8e-eps)
                             (dk-skolem!
                              (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                        (not (dk-contains? f 'DIST))))
                                       "the eps-over witness"))))
                   (r8e-epsu (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'POS-RR)
                                                       (dk-contains? f 'DIST)))
                                      "phi's eps universal"))
                   (r8e-del (begin
                              (dk-apply! r8e-epsu r8e-dd)
                              (dk-skolem!
                               (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                         (dk-contains? f 'DIST)))
                                        "phi's delta")))))
              (ew r8e-del)
              (dk-conj-close!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'POS-RR)
                     (ass)
                     (begin
                       (dk-peel!)
                       (let* ((r8e-b (cadr (caddr (cadr (dk-goal)))))
                              (r8e-w (list '(VADD m) (list r8e-hv 't)
                                           (list '(VNEG m) (list r8e-hv r8e-b)))))
                         (have! (list 'IN r8e-b 'RR)
                                (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
                         (fact 'fun-apply-type-c r8e-hv 'RR '(VEC m) r8e-b)
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hv 't))
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hv r8e-b))
                         (fact 'rkt-nvs-vneg-in-vec 'm (list r8e-hv r8e-b))
                         (fact 'nvs-vadd-in-vec 'm (list r8e-hv 't)
                               (list '(VNEG m) (list r8e-hv r8e-b)))
                         (fact 'vnrm-real 'm r8e-w)
                         ;; the two composite values
                         (let ((r8e-cva (r8e-capply r8e-hv)))
                           (dk-apply! r8e-cva 't)
                           (dk-apply! r8e-cva r8e-b))
                         (subst (list '= (list r8e-gh 't) (list 'g (list r8e-hv 't))))
                         (subst (list '= (list r8e-gh r8e-b) (list 'g (list r8e-hv r8e-b))))
                         ;; dist on RR is abs of the difference
                         (fact 'rr-ms-dist (list 'g (list r8e-hv 't))
                               (list 'g (list r8e-hv r8e-b)))
                         (subst (list '== (list '(DIST RR-MS)
                                                (list 'g (list r8e-hv 't))
                                                (list 'g (list r8e-hv r8e-b)))
                                      (list 'abs (list '- (list 'g (list r8e-hv 't))
                                                       (list 'g (list r8e-hv r8e-b))))))
                         ;; g(u) - g(v) = g(u - v)
                         (fact 'r8e-blf-sub 'm 'g (list r8e-hv 't) (list r8e-hv r8e-b))
                         (subst (list '= (list '- (list 'g (list r8e-hv 't))
                                               (list 'g (list r8e-hv r8e-b)))
                                      (list 'g r8e-w)))
                         ;; |g(w)| <= c ||w||,  ||w|| = dist(phi t, phi b) <= dd
                         (dk-apply! (r8e-bound) r8e-w)
                         (fact 'r8e-nvs-dist 'm (list r8e-hv 't) (list r8e-hv r8e-b))
                         ;; phi's delta universal AT b: dist(phi t, phi b) <= dd
                         (dk-apply! (dk-pick (lambda (f)
                                               (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f 'DIST)
                                                    (dk-contains? f r8e-del)))
                                             "phi's delta universal")
                                    r8e-b)
                         (have! (list '<= (list '(VNRM m) r8e-w) r8e-dd)
                                (lambda ()
                                  (subst (list '== (list '(VNRM m) r8e-w)
                                               (list '(DIST (NVS-METRIC-SPACE m))
                                                     (list r8e-hv 't) (list r8e-hv r8e-b))))
                                  (ass)))
                         (dk-apply! (dk-pick (lambda (f)
                                               (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f r8e-dd)
                                                    (not (dk-contains? f 'DIST))))
                                             "the eps-over universal")
                                    (list '(VNRM m) r8e-w))
                         ;; |g(w)| <= c ||w|| <= eps
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-w)
                         (fact 'rr-abs-closed (list 'g r8e-w))
                         (have! (list 'AND (list 'IN r8e-cv 'RR)
                                      (list 'IN (list '(VNRM m) r8e-w) 'RR)))
                         (fact 'rr-mul-closed r8e-cv (list '(VNRM m) r8e-w))
                         (fact 'rr-pos-rr-in-rr r8e-eps)
                         (fact 'rr-le-trans-c (list 'abs (list 'g r8e-w))
                               (list '* r8e-cv (list '(VNRM m) r8e-w)) r8e-eps)
                         (ass)))))))))))))
(r8e-check! 'r8e-blf-compose-continuous)

;;; =====================================================================
;;; (6) THE STEP LEMMA (the Hahn-Banach triage's gap (G1)): a bounded linear
;;; functional carries the vector Caratheodory derivative to the scalar one.
;;;
;;;   is-blf(m,g),  IS-DIFF-AT-V(m,h,t,L)   =>   IS-DIFF-AT(g o h, t, g(L))
;;;
;;; The factor is g o phi: its value at t is g(L); the identity is linearity
;;; twice (r8e-blf-sub on the left, homogeneity on the right); and its
;;; continuity at t is the ONE analytic step -- given eps, r8e-eps-over turns
;;; the bound c into a tolerance d on the norm, phi's own continuity supplies a
;;; delta for d, and |g(phi t) - g(phi b)| = |g(phi t - phi b)| <= c*||phi t -
;;; phi b|| = c*dist(phi t, phi b) <= eps.  No general three-space
;;; `compose-continuous-at' is needed (the tree's is RR-MS/RR-MS only).
;;;
;;; TWO DRIVER POINTS.
;;; * IS-BOUNDED-LINEAR-FUNCTIONAL is opened in have! LANES, not in the main
;;;   branch: `mac-h' is destructive and `gof-in-fun' / `r8e-blf-sub' are cited
;;;   below with the hypothesis itself as their antecedent.
;;; * the three hard conjuncts of the goal are proved as LANES before the
;;;   unfold, so the assembly after `ew' is four `ass'es.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (FORALL h (FORALL t (FORALL bl
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (IMPLIES (IS-DIFF-AT-V m h t bl)
          (IS-DIFF-AT (COMPOSE g h) t (g bl)))))))))))
(dk-peel!)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
(have! r8e-bnd                   (lambda () (r8e-blf-split!) (ass)))
(dk-split-all!
 (dk-landed (lambda () (mac-h 'IS-DIFF-AT-V '(IS-DIFF-AT-V m h t bl)))))
(have! '(== RR (PTS RR-MS)) (lambda () (slot 'PTS) (qrfl)))

(let* ((r8e-c   (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                      (dk-contains? f 'VNRM)))
                                     "the boundedness existential")))
       (r8e-phi (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                      (dk-contains? f 'IS-CONTINUOUS-AT)))
                                     "the Caratheodory factor")))
       (r8e-gph (list 'COMPOSE 'g r8e-phi))
       (r8e-gh  '(COMPOSE g h))
       ;; the bound at a vector:  abs(g w) <= c * ||w||
       (r8e-bound (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VNRM)
                                                       (dk-contains? f 'abs)))
                                      "the bound universal")))
       ;; the Caratheodory identity: the FORALL mentioning BOTH VADD and ACT
       (r8e-ident (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VADD)
                                                       (dk-contains? f 'ACT)))
                                      "the Caratheodory identity"))))
  (dk-split-all!)
  ;; phi's continuity is NOT unfolded here: (6a) is cited with it whole.
  ;; typings and the two beta laws, landed once for the whole proof
  (fact 'rr-is-set)
  (fact 'gof-in-fun 'm 'h 'g)
  (fact 'gof-in-fun 'm r8e-phi 'g)
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR 'bl)
  (fact 'fun-apply-type-c 'h 'RR '(VEC m) 't)
  (fact 'fun-apply-type-c r8e-phi 'RR '(VEC m) 't)
  (have! (list 'AND (list 'IN 'h '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'h)
  (have! (list 'AND (list 'IN r8e-phi '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g r8e-phi)

  ;; ---- LANE 1: g o phi is continuous at t (section 6a) ----------------
  (have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS r8e-gph 't)
         (lambda ()
           (fact 'r8e-blf-compose-continuous 'm 'g r8e-phi 't)
           (ass)))

  ;; ---- LANE 2: (g o phi)(t) = g(L) ------------------------------------
  (have! (list '= (list r8e-gph 't) '(g bl))
   (lambda ()
     (dk-apply! (r8e-capply r8e-phi) 't)
     (subst (list '= (list r8e-gph 't) (list 'g (list r8e-phi 't))))
     (subst (list '= (list r8e-phi 't) 'bl))
     (rfl)))

  ;; ---- LANE 3: the Caratheodory identity for g o h ---------------------
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
           (list '= (list '- (list r8e-gh 'x_) (list r8e-gh 't))
                 (list '* (list r8e-gph 'x_) (list '- 'x_ 't)))))
   (lambda ()
     (dk-peel!)
     (let ((r8e-x (cadr (cadr (cadr (dk-goal))))))
       (fact 'fun-apply-type-c 'h 'RR '(VEC m) r8e-x)
       (fact 'fun-apply-type-c r8e-phi 'RR '(VEC m) r8e-x)
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list 'h r8e-x))
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR '(h t))
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-phi r8e-x))
       (fact 'rr-sub-in-rr r8e-x 't)
       (let ((r8e-cah (r8e-capply 'h))
             (r8e-cap (r8e-capply r8e-phi)))
         (dk-apply! r8e-cah r8e-x)
         (dk-apply! r8e-cah 't)
         (dk-apply! r8e-cap r8e-x))
       (subst (list '= (list r8e-gh r8e-x) (list 'g (list 'h r8e-x))))
       (subst (list '= (list r8e-gh 't) '(g (h t))))
       (subst (list '= (list r8e-gph r8e-x) (list 'g (list r8e-phi r8e-x))))
       (fact 'r8e-blf-sub 'm 'g (list 'h r8e-x) '(h t))
       (subst (list '= (list '- (list 'g (list 'h r8e-x)) '(g (h t)))
                    (list 'g (list '(VADD m) (list 'h r8e-x) '((VNEG m) (h t))))))
       (subst (dk-apply! (r8e-ident) r8e-x))
       (subst (dk-apply! (r8e-homogeneity) (list '- r8e-x 't) (list r8e-phi r8e-x)))
       (crs))))

  ;; ---- the assembly ---------------------------------------------------
  (mac 'IS-DIFF-AT)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'FORSOME)
         (begin (ew r8e-gph) (dk-conj-close! (lambda () (ass))))
         (ass)))))
(r8e-check! 'r8e-blf-diff-commute)

;;; =====================================================================
;;; (7) FROM TOTALITY TO DIFFERENTIABILITY -- what closes the triage's gap
;;; (G2).  f^(j) and f^(j+1) total means DERIV-V(m, f^(j), x) DENOTES at every
;;; real x, and `iota-e' (pi-iota-in-elim!, ADDED 2026-09-15, one day after the
;;; note at vector-taylor-proof.scm:410 declared the principle missing) turns
;;; that into the defining property.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL f (FORALL j_ (FORALL x_
        (IMPLIES (IN j_ NN) (IMPLIES (IN x_ RR)
        (IMPLIES (IN (NTH-DERIV-V m f j_) (FUN RR (VEC m)))
        (IMPLIES (IN (NTH-DERIV-V m f (succ j_)) (FUN RR (VEC m)))
          (IS-DIFF-AT-V m (NTH-DERIV-V m f j_) x_
                        ((NTH-DERIV-V m f (succ j_)) x_))))))))))))
(dk-peel!)
(let* ((r8e-hj '(NTH-DERIV-V m f j_))
       (r8e-hs '(NTH-DERIV-V m f (succ j_)))
       (r8e-dv (list 'DERIV-V 'm r8e-hj 'x_))
       (r8e-io (list 'IOTA 'L (list 'IS-DIFF-AT-V 'm r8e-hj 'x_ 'L))))
  (fact 'fun-apply-type-c r8e-hs 'RR '(VEC m) 'x_)
  (have! (list '== (list r8e-hs 'x_) r8e-dv)
         (lambda () (mac 'nth-deriv-v-succ) (lam-b) (qrfl)))
  (have! (list '== r8e-dv r8e-io) (lambda () (mac 'DERIV-V) (qrfl)))
  (have! (list 'IN r8e-io '(VEC m))
         (lambda ()
           (subst (list '== r8e-io r8e-dv))
           (subst (list '== r8e-dv (list r8e-hs 'x_)))
           (ass)))
  (iota-e r8e-io)
  (subst (list '== (list r8e-hs 'x_) r8e-dv))
  (subst (list '== r8e-dv r8e-io))
  (ass))
(r8e-check! 'r8e-nth-deriv-v-diff)

;;; =====================================================================
;;; (8) THE COMMUTATION, as an identity of FUNCTIONS, by induction on k:
;;;        (g o f)^(k)  =  g o f^(k)
;;; The induction variable is OUTERMOST (`ni' tests the literal shape).  The
;;; step is: the IH rewrites (g o f)^(k) to g o f^(k) under the recursion
;;; axiom, (7) + (6) + `deriv-of-is-diff-at' compute its derivative at every
;;; point as g(f^(k+1)(x)), and `fun-domain-extensionality' closes.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
       (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'k)
           '(= (NTH-DERIV (COMPOSE g f) k)
               (COMPOSE g (NTH-DERIV-V m f k)))))))))))))
(let* ((r8e-lv (dk-opened (lambda () (ni))))
       (r8e-base (r8e-leaf r8e-lv (lambda (g) (not (dk-contains? g 'succ))) "the base"))
       (r8e-step (r8e-leaf r8e-lv (lambda (g) (dk-contains? g 'succ)) "the step")))
  ;; ---- base: (g o f)^(0) = g o f ------------------------------------
  (dk-focus! r8e-base)
  (dk-peel!)
  (fact 'gof-in-fun 'm 'f 'g)
  (mac 'nth-deriv-zero)
  (mac 'nth-deriv-v-zero)
  (rfl)
  ;; ---- step ---------------------------------------------------------
  (dk-focus! r8e-step)
  (dk-peel!)
  (let* ((r8e-gl  (dk-goal))
         (r8e-lhs (cadr r8e-gl))
         (r8e-rhs (caddr r8e-gl))
         (r8e-gof (cadr r8e-lhs))
         (r8e-g   (cadr r8e-gof))
         (r8e-f   (caddr r8e-gof))
         (r8e-sk  (caddr r8e-lhs))
         (r8e-k   (cadr r8e-sk))
         (r8e-hs  (caddr r8e-rhs))
         (r8e-m   (cadr r8e-hs))
         (r8e-hk  (list 'NTH-DERIV-V r8e-m r8e-f r8e-k))
         (r8e-ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f 'NTH-DERIV)))
                           "the induction hypothesis"))
         (r8e-df  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f 'NTH-DERIV-V)
                                            (dk-contains? f 'FUN)))
                           "DFUN-V(m,f,succ k)")))
    (fact 'nn-succ-closed r8e-k)
    (fact 'nn-le-succ r8e-k)
    (fact 'nn-le-refl r8e-sk)
    ;; the two typings out of DFUN-V(m,f,succ k)
    (have! (list 'AND (list 'IN r8e-k 'NN) (list '<= r8e-k r8e-sk)))
    (dk-apply! r8e-df r8e-k)
    (have! (list 'AND (list 'IN r8e-sk 'NN) (list '<= r8e-sk r8e-sk)))
    (dk-apply! r8e-df r8e-sk)
    ;; the induction hypothesis, at DFUN-V(m,f,k)
    (fact 'dfun-v-mono r8e-m r8e-f r8e-sk r8e-k)
    (let* ((r8e-ek (dk-apply! r8e-ih r8e-m r8e-f r8e-g))
           (r8e-p3 (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                     (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) 'x_)
                           (list r8e-g (list r8e-hs 'x_)))))))
      (have! (list 'IN r8e-g (list 'FUN (list 'VEC r8e-m) 'RR))
             (lambda () (r8e-blf-split! r8e-m r8e-g) (ass)))
      (fact 'gof-in-fun r8e-m r8e-hs r8e-g)
      (fact 'gof-in-fun r8e-m r8e-hk r8e-g)
      ;; the derivative of g o f^(k) at every point
      (have! r8e-p3
       (lambda ()
         (dk-peel!)
         (let ((r8e-x (caddr (cadr (dk-goal)))))
           (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
           (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR (list r8e-hs r8e-x))
           (fact 'r8e-nth-deriv-v-diff r8e-m r8e-f r8e-k r8e-x)
           (fact 'r8e-blf-diff-commute r8e-m r8e-g r8e-hk r8e-x (list r8e-hs r8e-x))
           (fact 'deriv-of-is-diff-at (list 'COMPOSE r8e-g r8e-hk) r8e-x
                 (list r8e-g (list r8e-hs r8e-x)))
           (ass))))
      ;; (g o f)^(succ k) is a total real function
      (have! (list 'IN r8e-lhs '(FUN RR RR))
       (lambda ()
         (mac 'nth-deriv-succ)
         (for-each
          (lambda (r8e-lf)
            (dk-focus! r8e-lf)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'rr-is-set) (ass))
                (begin
                  (dk-peel!)
                  (let ((r8e-x (caddr (cadr (dk-goal)))))
                    (dk-apply! r8e-p3 r8e-x)
                    (subst r8e-ek)
                    (subst (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) r8e-x)
                                 (list r8e-g (list r8e-hs r8e-x))))
                    (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
                    (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR
                          (list r8e-hs r8e-x))
                    (ass)))))
          (dk-opened (lambda () (lam-t))))))
      ;; both sides are members of FUN(RR), and agree pointwise
      (have! (list 'IN r8e-lhs '(FUN RR))
             (lambda ()
               (dk-split-all!
                (dk-landed (lambda () (mac-h 'fun-codomain-iff
                                             (list 'IN r8e-lhs '(FUN RR RR))))))
               (ass)))
      (have! (list 'IN r8e-rhs '(FUN RR))
             (lambda ()
               (dk-split-all!
                (dk-landed (lambda () (mac-h 'fun-codomain-iff
                                             (list 'IN r8e-rhs '(FUN RR RR))))))
               (ass)))
      (have! (list 'AND (list 'IN r8e-hs (list 'FUN 'RR (list 'VEC r8e-m)))
                   (list 'IN r8e-g (list 'FUN (list 'VEC r8e-m) 'RR))))
      (fact 'compose-apply 'RR (list 'VEC r8e-m) 'RR r8e-g r8e-hs)
      (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                (list '= (list r8e-lhs 'x_) (list r8e-rhs 'x_))))
       (lambda ()
         (dk-peel!)
         (let ((r8e-x (cadr (cadr (dk-goal)))))
           (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
           (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR (list r8e-hs r8e-x))
           (dk-apply! r8e-p3 r8e-x)
           (dk-apply! (r8e-capply r8e-hs) r8e-x)
           (mac 'nth-deriv-succ)
           (lam-b)
           (subst r8e-ek)
           (subst (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) r8e-x)
                        (list r8e-g (list r8e-hs r8e-x))))
           (subst (list '= (list r8e-rhs r8e-x) (list r8e-g (list r8e-hs r8e-x))))
           (rfl))))
      (fact 'fun-domain-extensionality 'RR r8e-lhs r8e-rhs)
      (ass))))
(r8e-check! 'r8e-gof-nth-deriv-fn)

;;; =====================================================================
;;; (9) THE LEAF `gof-nth-deriv', GUARDED.  Binders m f g n t and the body are
;;; the support's (vector-taylor-proof.scm:656-662) unchanged.  The two added
;;; antecedents are exactly what the note at vector-taylor-proof.scm:370
;;; predicted, and BOTH are in the citer's context at :751:
;;;   DFUN-V(m,f,n)      -- taylor-v-derivs-in-fun, already cited at :707;
;;;   IS-DIFF-AT-V(m, f^(n), t, f^(n+1)(t))
;;;                      -- the second conjunct of TAYLOR-DIFFERENTIABLE-V at
;;;                         (n, theta), theta being interior.
;;; Without them f^(n+1)(t) is an IOTA with no satisfier and the support's
;;; strict `=' is FALSE (both sides undefined).
;;;
;;; NOTE the order of the last two steps: `nth-deriv-succ' and `lam-b' FIRST,
;;; so that (g o f)^(n+1)(t) becomes DERIV((g o f)^(n), t) and the commutation
;;; (8) is needed only at n.  f^(n+1) is NOT assumed total -- which matters,
;;; because TAYLOR-DIFFERENTIABLE-V does not make it so.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'n (list 'FORALL 't
       (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
       (list 'IMPLIES '(IN f (FUN RR (VEC m)))
       (list 'IMPLIES '(IN n NN)
       (list 'IMPLIES '(IN t RR)
       (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
       (list 'IMPLIES '(IS-DIFF-AT-V m (NTH-DERIV-V m f n)
                                     t ((NTH-DERIV-V m f (succ n)) t))
         '(= ((NTH-DERIV (COMPOSE g f) (succ n)) t)
             (g ((NTH-DERIV-V m f (succ n)) t))))))))))))))))
(dk-peel!)
(let* ((r8e-hn '(NTH-DERIV-V m f n))
       (r8e-hs '(NTH-DERIV-V m f (succ n)))
       (r8e-gh (list 'COMPOSE 'g r8e-hn)))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (fact 'diff-v-value-in-vec 'm r8e-hn 't (list r8e-hs 't))
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs 't))
  (fact 'r8e-blf-diff-commute 'm 'g r8e-hn 't (list r8e-hs 't))
  (fact 'deriv-of-is-diff-at r8e-gh 't (list 'g (list r8e-hs 't)))
  (fact 'r8e-gof-nth-deriv-fn 'n 'm 'f 'g)
  (mac 'nth-deriv-succ)
  (lam-b)
  (subst (list '= '(NTH-DERIV (COMPOSE g f) n) r8e-gh))
  (subst (list '= (list 'DERIV r8e-gh 't) (list 'g (list r8e-hs 't))))
  (rfl))
(r8e-check! 'gof-nth-deriv-dfun)
(alias! 'gof-nth-deriv-dfun
        "a bounded linear functional commutes with the (n+1)-st vector derivative")

;;; =====================================================================
;;; (10) THE LEAF `gof-taylor-diff', GUARDED.  Binders m f g a x n and the body
;;; are the support's (vector-taylor-proof.scm:627-632); the added antecedents
;;; are IS-NORMED-VECTOR-SPACE(m) (TAYLOR-DIFFERENTIABLE-V does not carry it,
;;; and the linearity bricks need it), (IN n NN), and DFUN-V(m,f,n) -- which
;;; `taylor-v-derivs-in-fun' gives the citer at :707.
;;;
;;; Each conjunct is (8) at k <= n rewriting (g o f)^(k) to g o f^(k), and then:
;;; the continuity conjunct is (6a) at f^(k); the differentiability conjunct is
;;; `nth-deriv-succ' + `lam-b' + the step lemma (6) at the IS-DIFF-AT-V the
;;; hypothesis already carries, so f^(k+1) is never assumed total.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
       (list 'FORALL 'x (list 'FORALL 'n
         (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES '(IN n NN)
         (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE-V m f a x n)
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
           '(TAYLOR-DIFFERENTIABLE (COMPOSE g f) a x n)))))))))))))))
(dk-peel!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'taylor-differentiable-v
                              '(TAYLOR-DIFFERENTIABLE-V m f a x n)))))
(let* ((r8e-cont (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'IS-CONTINUOUS-AT)))
                          "the continuity conjunct of TD-V"))
       (r8e-diff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'IS-DIFF-AT-V)))
                          "the differentiability conjunct of TD-V"))
       (r8e-df   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'NTH-DERIV-V)
                                           (dk-contains? f 'FUN)))
                          "DFUN-V(m,f,n)")))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (mac 'TAYLOR-DIFFERENTIABLE)
  (dk-conj-close!
   (lambda ()
     (let ((r8e-cc (dk-contains? (dk-goal) 'IS-CONTINUOUS-AT)))
       (dk-peel!)
       (let* ((r8e-gl (dk-goal))
              (r8e-nd (if r8e-cc (list-ref r8e-gl 3) (cadr r8e-gl)))
              (r8e-k  (caddr r8e-nd))
              (r8e-t  (if r8e-cc (list-ref r8e-gl 4) (caddr r8e-gl)))
              (r8e-hk (list 'NTH-DERIV-V 'm 'f r8e-k))
              (r8e-hs (list 'NTH-DERIV-V 'm 'f (list 'succ r8e-k)))
              (r8e-gh (list 'COMPOSE 'g r8e-hk)))
         (dk-split-all!)
         (fact 'dfun-v-mono 'm 'f 'n r8e-k)
         (have! (list 'AND (list 'IN r8e-k 'NN) (list '<= r8e-k 'n)))
         (dk-apply! r8e-df r8e-k)                    ; f^(k) is total
         (fact 'r8e-gof-nth-deriv-fn r8e-k 'm 'f 'g)
         (if r8e-cc
             (begin                              ; ---- the continuity conjunct
               (subst (list '= r8e-nd r8e-gh))
               (dk-apply! r8e-cont r8e-k r8e-t)
               (fact 'r8e-blf-compose-continuous 'm 'g r8e-hk r8e-t)
               (ass))
             (begin                              ; ---- the differentiability conjunct
               ;; dk-split-all! above broke the interior guard into its two
               ;; halves; TD-V's universal wants it back as ONE conjunction.
               (have! (list 'AND
                            (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '<)
                                                      (equal? (caddr f) r8e-t)))
                                     "a < t")
                            (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '<)
                                                      (equal? (cadr f) r8e-t)))
                                     "t < x")))
               (dk-apply! r8e-diff r8e-k r8e-t)
               (let ((r8e-dv (list 'IS-DIFF-AT-V 'm r8e-hk r8e-t (list r8e-hs r8e-t))))
                 (have! (list 'IN r8e-t 'RR)
                        (lambda ()
                          (dk-split-all!
                           (dk-landed (lambda () (mac-h 'is-diff-at-v r8e-dv))))
                          (ass))))
               (fact 'diff-v-value-in-vec 'm r8e-hk r8e-t (list r8e-hs r8e-t))
               (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs r8e-t))
               (fact 'r8e-blf-diff-commute 'm 'g r8e-hk r8e-t (list r8e-hs r8e-t))
               (fact 'deriv-of-is-diff-at r8e-gh r8e-t (list 'g (list r8e-hs r8e-t)))
               ;; (g o f)^(k+1)(t) = DERIV((g o f)^(k), t): the commutation is
               ;; then needed only at k.
               (mac 'nth-deriv-succ)
               (lam-b)
               (subst (list '= r8e-nd r8e-gh))
               (subst (list '= (list 'DERIV r8e-gh r8e-t)
                            (list 'g (list r8e-hs r8e-t))))
               (ass))))))))
(r8e-check! 'gof-taylor-diff-dfun)
(alias! 'gof-taylor-diff-dfun
        "a bounded linear functional preserves Taylor differentiability")

;;; =====================================================================
;;; (11) THE PROJECTION THE CITER NEEDS.  gof-nth-deriv-dfun asks for
;;; IS-DIFF-AT-V(m, f^(n), t, f^(n+1)(t)) at the interior point; that is the
;;; second conjunct of TAYLOR-DIFFERENTIABLE-V at (n, t), and nothing in the
;;; tree surfaced it (taylor-v-deriv-in-vec unfolds TD-V for the TYPING only).
;;; With this, the citation at vector-taylor-proof.scm:751 is two lines.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
        (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
        (IMPLIES (IN n NN)
        (IMPLIES (< a t) (IMPLIES (< t x)
          (IS-DIFF-AT-V m (NTH-DERIV-V m f n) t
                        ((NTH-DERIV-V m f (succ n)) t))))))))))))))
(dk-peel!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'taylor-differentiable-v
                              '(TAYLOR-DIFFERENTIABLE-V m f a x n)))))
(fact 'nn-le-refl 'n)
(have! '(AND (IN n NN) (<= n n)))
(have! '(AND (< a t) (< t x)))
(dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     (dk-contains? f 'IS-DIFF-AT-V)))
                    "the differentiability conjunct of TD-V")
           'n 't)
(ass)
(r8e-check! 'r8e-td-v-diff-at)
(alias! 'r8e-td-v-diff-at
        "a Taylor-differentiable curve is vector-differentiable at an interior point")

;;; =====================================================================
;;; (12) THE LEAF `g-of-remainder', GUARDED.
;;;
;;; Three utilities first: the TAYLOR-POLY unfold as a THEOREM (a def-functoid
;;; installs only a macete, and `subst' needs a named equation to go BACKWARDS
;;; from SERIES-PARTIAL-SUM to TAYLOR-POLY -- CLAUDE.md, "where a definition
;;; lives"), and two arithmetic identities stated with the coefficient
;;; QUANTIFIED, because `crs' declines any goal containing `recip'.
;;; =====================================================================
(sp (make-wff
     '(FORALL ff (FORALL aa (FORALL nd (FORALL xx
        (== (TAYLOR-POLY ff aa nd xx)
            (SERIES-PARTIAL-SUM
              (VNB-LAMBDA k NN (* (* ((NTH-DERIV ff k) aa) (power (- xx aa) k))
                                  (recip (FACTORIAL k))))
              (succ nd)))))))))
(dk-peel!)
(mac 'TAYLOR-POLY)
(qrfl)
(r8e-check! 'r8e-tp-unfold)

(sp (make-wff
     '(FORALL p_ (IMPLIES (IN p_ RR)
        (FORALL q_ (IMPLIES (IN q_ RR)
        (FORALL v_ (IMPLIES (IN v_ RR)
          (= (* (* p_ q_) v_) (* (* v_ p_) q_))))))))))
(dk-peel!)
(crs)
(r8e-check! 'r8e-coef-comm)

(sp (make-wff '(FORALL y_ (IMPLIES (IN y_ RR) (= (+ 0 y_) y_)))))
(dk-peel!)
(crs)
(r8e-check! 'r8e-zero-add)

;;; ---- the coefficient (x-a)^k / k!, and the summand of TAYLOR-POLY -------
(define (r8e-coef k) (list '* (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
(define (r8e-coef-real! k)
  (fact 'rr-sub-in-rr 'x 'a)
  (fact 'power-closed-at k '(- x a))
  (fact 'recip-factorial-in-rr k)
  (have! (list 'AND (list 'IN (list 'power '(- x a) k) 'RR)
               (list 'IN (list 'recip (list 'FACTORIAL k)) 'RR)))
  (fact 'rr-mul-closed (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
(define r8e-lam
  '(VNB-LAMBDA k NN (* (* ((NTH-DERIV (COMPOSE g f) k) a) (power (- x a) k))
                       (recip (FACTORIAL k)))))
;;; (IN (g (f^(k)(a))) RR), by the commutation (8) -- the value of the k-th
;;; summand once the derivative has been pushed through g.
(define (r8e-gval k) (list 'g (list (list 'NTH-DERIV-V 'm 'f k) 'a)))
(define (r8e-product-real! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;;; =====================================================================
;;; (12a) g of the vector Taylor polynomial IS the scalar Taylor polynomial of
;;; g o f, by induction on n.  n is OUTERMOST (`ni' tests the literal shape);
;;; the leaf's own binder order comes back in (12b) by one `fact'.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
       (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
         (list 'FORALL 'x
           (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
           (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
           (list 'IMPLIES '(IN f (FUN RR (VEC m)))
           (list 'IMPLIES '(IN a RR)
           (list 'IMPLIES '(IN x RR)
           (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
             '(= (g (TAYLOR-POLY-V m f a x n))
                 (TAYLOR-POLY (COMPOSE g f) a n x)))))))))))))))))
(define r8e-br (use-induction))
(define r8e-nv (cdr (assq 'var r8e-br)))
(define r8e-ih (cdr (assq 'ih  r8e-br)))

;;; ---- base: n = 0 ------------------------------------------------------
(dk-focus! (cdr (assq 'base r8e-br)))
(dk-peel-to! '=)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
(fact 'nn-zero-in)
(fact 'rr-zero-in)
(fact 'gof-in-fun 'm 'f 'g)
(fact 'fun-apply-type-c 'f 'RR '(VEC m) 'a)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR '(f a))
(r8e-coef-real! 0)
(have! '(AND (IN f (FUN RR (VEC m))) (IN g (FUN (VEC m) RR))))
(fact 'compose-apply 'RR '(VEC m) 'RR 'g 'f)
(dk-apply! (r8e-capply 'f) 'a)
(fact 'r8e-tp-unfold '(COMPOSE g f) 'a 0 'x)
(fact 'series-partial-sum-zero r8e-lam)
(have! (list 'IN (list 'SERIES-PARTIAL-SUM r8e-lam 0) 'RR)
       (lambda () (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam 0) 0)) (ass)))
(have! (list 'IN (list r8e-lam 0) 'RR)
       (lambda ()
         (lam-b)
         (mac 'nth-deriv-zero)
         (subst '(= ((COMPOSE g f) a) (g (f a))))
         (r8e-product-real! '(g (f a)) (list 'power '(- x a) 0))
         (r8e-product-real! (list '* '(g (f a)) (list 'power '(- x a) 0))
                            (list 'recip (list 'FACTORIAL 0)))
         (ass)))
(fact 'series-partial-sum-succ r8e-lam 0)
(mac 'taylor-poly-v-zero)
(mac 'nth-deriv-v-zero)
(subst (dk-apply! r8e-lin-hom (r8e-coef 0) '(f a)))
(subst (list '= '(TAYLOR-POLY (COMPOSE g f) a 0 x)
             (list 'SERIES-PARTIAL-SUM r8e-lam '(succ 0))))
(subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam '(succ 0))
             (list '+ (list 'SERIES-PARTIAL-SUM r8e-lam 0) (list r8e-lam 0))))
(subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam 0) 0))
(lam-b)
(mac 'nth-deriv-zero)
(subst '(= ((COMPOSE g f) a) (g (f a))))
(fact 'r8e-coef-comm (list 'power '(- x a) 0) (list 'recip (list 'FACTORIAL 0)) '(g (f a)))
(subst (list '= (list '* (r8e-coef 0) '(g (f a)))
             (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))))
(r8e-product-real! '(g (f a)) (list 'power '(- x a) 0))
(r8e-product-real! (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))
(fact 'r8e-zero-add (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                          (list 'recip (list 'FACTORIAL 0))))
(subst (list '= (list '+ 0 (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                                  (list 'recip (list 'FACTORIAL 0))))
             (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))))
(rfl)

;;; ---- step -------------------------------------------------------------
(dk-focus! (cdr (assq 'step r8e-br)))
(dk-peel-to! '=)
(let* ((r8e-dfs (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (dk-contains? f 'NTH-DERIV-V)
                                          (dk-contains? f 'FUN)))
                         "DFUN-V(m,f,succ n)"))
       (r8e-sn (list 'succ r8e-nv))
       (r8e-hs (list 'NTH-DERIV-V 'm 'f r8e-sn))
       (r8e-tv (list 'TAYLOR-POLY-V 'm 'f 'a 'x r8e-nv))
       (r8e-cf (r8e-coef r8e-sn))
       (r8e-vl (list 'g (list r8e-hs 'a))))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
  (have! r8e-lin-add               (lambda () (r8e-blf-split!) (ass)))
  (fact 'nn-succ-closed r8e-nv)
  (fact 'nn-le-succ r8e-nv)
  (fact 'gof-in-fun 'm 'f 'g)
  (fact 'dfun-v-mono 'm 'f r8e-sn r8e-nv)
  ;; the induction hypothesis at this m f g a x
  (let ((r8e-ihi (dk-apply! r8e-ih 'm 'f 'g 'a 'x)))
    ;; typings: the polynomial, the (n+1)-st derivative value, the coefficient
    (fact 'vtaylor-poly-in-vec 'm 'f 'a 'x r8e-nv)
    (fact 'nth-deriv-v-in-vec 'm 'f r8e-sn 'a)
    (r8e-coef-real! r8e-sn)
    (fact 'nvs-act-in-vec 'm r8e-cf (list r8e-hs 'a))
    (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-tv)
    (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs 'a))
    ;; the commutation (8) at succ n, and the beta law of g o f^(succ n)
    (fact 'r8e-gof-nth-deriv-fn r8e-sn 'm 'f 'g)
    (fact 'nn-le-refl r8e-sn)
    (have! (list 'AND (list 'IN r8e-sn 'NN) (list '<= r8e-sn r8e-sn)))
    (dk-apply! r8e-dfs r8e-sn)                  ; f^(succ n) is total
    (have! (list 'AND (list 'IN r8e-hs '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
    (fact 'compose-apply 'RR '(VEC m) 'RR 'g r8e-hs)
    (dk-apply! (r8e-capply r8e-hs) 'a)
    ;; the two unfolds of TAYLOR-POLY, and the partial-sum recurrence
    (fact 'r8e-tp-unfold '(COMPOSE g f) 'a r8e-nv 'x)
    (fact 'r8e-tp-unfold '(COMPOSE g f) 'a r8e-sn 'x)
    (have! (list 'IN (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv)) 'RR)
           (lambda ()
             (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv))
                          (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)))
             (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)
                          (list 'g r8e-tv)))
             (ass)))
    (have! (list 'IN (list r8e-lam r8e-sn) 'RR)
           (lambda ()
             (lam-b)
             (subst (list '= (list 'NTH-DERIV '(COMPOSE g f) r8e-sn)
                          (list 'COMPOSE 'g r8e-hs)))
             (subst (list '= (list (list 'COMPOSE 'g r8e-hs) 'a) r8e-vl))
             (r8e-product-real! r8e-vl (list 'power '(- x a) r8e-sn))
             (r8e-product-real! (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                                (list 'recip (list 'FACTORIAL r8e-sn)))
             (ass)))
    (fact 'series-partial-sum-succ r8e-lam r8e-sn)
    ;; ---- the goal
    (mac 'taylor-poly-v-succ)
    (subst (dk-apply! r8e-lin-add r8e-tv (list (list 'ACT 'm) r8e-cf (list r8e-hs 'a))))
    (subst (dk-apply! r8e-lin-hom r8e-cf (list r8e-hs 'a)))
    (subst r8e-ihi)
    (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-sn 'x)
                 (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-sn))))
    (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-sn))
                 (list '+ (list 'SERIES-PARTIAL-SUM r8e-lam r8e-sn)
                       (list r8e-lam r8e-sn))))
    (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)
                 (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv))))
    (lam-b)
    (subst (list '= (list 'NTH-DERIV '(COMPOSE g f) r8e-sn)
                 (list 'COMPOSE 'g r8e-hs)))
    (subst (list '= (list (list 'COMPOSE 'g r8e-hs) 'a) r8e-vl))
    (fact 'r8e-coef-comm (list 'power '(- x a) r8e-sn)
          (list 'recip (list 'FACTORIAL r8e-sn)) r8e-vl)
    (subst (list '= (list '* r8e-cf r8e-vl)
                 (list '* (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                       (list 'recip (list 'FACTORIAL r8e-sn)))))
    ;; `rfl' is strict: the REDUCED summand must be typed, not just the
    ;; unreduced (LAM (succ n)) the recurrence was cited with.
    (r8e-product-real! r8e-vl (list 'power '(- x a) r8e-sn))
    (r8e-product-real! (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                       (list 'recip (list 'FACTORIAL r8e-sn)))
    (rfl)))
(r8e-check! 'r8e-g-of-poly-ind)

;;; =====================================================================
;;; (12b) THE LEAF `g-of-remainder', GUARDED.  Binders m f g a x n and the body
;;; are the support's (vector-taylor-proof.scm:641-647) unchanged; the added
;;; antecedents are IS-NORMED-VECTOR-SPACE(m) and DFUN-V(m,f,n) -- the latter
;;; is what `vtaylor-poly-in-vec' and (12a) both need, and the citer holds it
;;; at :707.  Without it TAYLOR-POLY-V applies ACT to f^(k)(a), an IOTA with no
;;; satisfier, and the support's strict `=' is FALSE.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
       (list 'FORALL 'x (list 'FORALL 'n
         (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES '(IN a RR)
         (list 'IMPLIES '(IN x RR)
         (list 'IMPLIES '(IN n NN)
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
           '(= (g ((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))))
               (- ((COMPOSE g f) x)
                  (TAYLOR-POLY (COMPOSE g f) a n x))))))))))))))))))
(dk-peel!)
(let ((r8e-pv '(TAYLOR-POLY-V m f a x n)))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (fact 'fun-apply-type-c 'f 'RR '(VEC m) 'x)
  (fact 'vtaylor-poly-in-vec 'm 'f 'a 'x 'n)
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR '(f x))
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-pv)
  (fact 'gof-in-fun 'm 'f 'g)
  (have! '(AND (IN f (FUN RR (VEC m))) (IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'f)
  (dk-apply! (r8e-capply 'f) 'x)
  ;; g(f(x) (-) P) = g(f(x)) - g(P)
  (subst (dk-fact! 'r8e-blf-sub 'm 'g '(f x) r8e-pv))
  ;; (g o f)(x) = g(f(x))  and  TAYLOR-POLY(g o f, a, n, x) = g(P)
  (subst '(= ((COMPOSE g f) x) (g (f x))))
  (fact 'r8e-g-of-poly-ind 'n 'm 'f 'g 'a 'x)
  (subst (list '= '(TAYLOR-POLY (COMPOSE g f) a n x) (list 'g r8e-pv)))
  (rfl))
(r8e-check! 'g-of-remainder-dfun)
(alias! 'g-of-remainder-dfun
        "a bounded linear functional turns the vector Taylor remainder into the scalar one")

;;; =====================================================================
;;; WHAT THE THREE CITATIONS IN vector-taylor-proof.scm BECOME
;;;   :723  (fact 'gof-taylor-diff 'm 'f G 'a 'x 'n)
;;;      -> (fact 'gof-taylor-diff-dfun 'm 'f G 'a 'x 'n)
;;;   :750  (fact 'g-of-remainder 'm 'f G 'a 'x 'n)
;;;      -> (fact 'g-of-remainder-dfun 'm 'f G 'a 'x 'n)
;;;   :751  (fact 'gof-nth-deriv 'm 'f G 'n THETA)
;;;      -> (fact 'r8e-td-v-diff-at 'm 'f 'a 'x 'n THETA)   [new line]
;;;         (fact 'gof-nth-deriv-dfun 'm 'f G 'n THETA)
;;; Every antecedent of the three guarded theorems is in that proof's context
;;; at those lines: IS-NORMED-VECTOR-SPACE(m), IS-BOUNDED-LINEAR-FUNCTIONAL(m,G),
;;; f in FUN(RR,VEC m), a, x in RR, n in NN and (< a THETA), (< THETA x) from
;;; ANT1 and the taylor-lagrange existential, and DFUN-V(m,f,n) from the
;;; `taylor-v-derivs-in-fun' citation already at :707.
;;; =====================================================================
