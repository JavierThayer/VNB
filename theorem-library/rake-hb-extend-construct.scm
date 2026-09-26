;;; rake-hb-extend-construct.scm -- hb-extend-construct (theorem-library/
;;; hahn-banach-proof.scm:44), rake batch 7, assignment 7-C, second leaf.
;;;
;;;   m a real NVS, s a submodule, f a linear functional on s, v in VEC(m) with
;;;   v NOT in s, alpha any real  =>  there is a linear functional g on
;;;   SPAN-ADD-ONE(m,s,v) = s + RR.v extending f, with g(y + r.v) = f(y) + r*alpha.
;;;
;;; THE STATEMENT IS TRUE AS WRITTEN (checked before proving): `v not in s' is
;;; exactly what makes the decomposition y + r.v unique, and uniqueness is what
;;; the construction needs -- no further guard is missing.
;;;
;;; THE CONSTRUCTION.  The decomposition is unique but is not a TERM, so g is
;;; built from a definite description:
;;;
;;;   g = VNB-LAMBDA u in SPAN-ADD-ONE(m,s,v).
;;;         IOTA t. t in RR and (some p in s, c in RR with u = p + c.v
;;;                              and t = f(p) + c*alpha)
;;;
;;; typed by `lam-t', reduced by `lam-b', and pinned by `hbx-value' (the IOTA
;;; denotes and its value is f(p) + c*alpha), which is proved by `iota-d' from
;;; `hbx-decomp-unique'.  Same shape as theorem-library/rake-line-functional.scm
;;; one dimension lower, and the model for an IOTA-defined operator is
;;; theorem-library/rake-esup-defined.scm.
;;;
;;; THE CONTENT is `hbx-decomp-unique': p1 + c1.v = p2 + c2.v with p1,p2 in s
;;; and v outside s forces c1 = c2 and p1 = p2.  If c1 /= c2 then
;;; (c1-c2).v = (-p1) + p2 lies in s, and so does v = (1/(c1-c2)).((c1-c2).v),
;;; against the hypothesis.  It rests on CANCELLATION in the vector group
;;; (`nvs-vadd-cancel' / `-right'), which the tree did not have for a normed
;;; vector space and which was proved here on 2026-09-19 from the is-identity /
;;; has-inverses / is-associative / is-commutative conjuncts of
;;; IS-NORMED-VECTOR-SPACE.  Since batch 8 those eleven vector-group theorems
;;; live in theorem-library/nvs-act-laws.scm (see the note at section (1)
;;; below); this file CITES them.
;;;
;;; ALL TWELVE THEOREMS LEFT HERE ARE `modulo 0'.
;;;
;;; LOAD WINDOW: any slot after theorem-library/nvs-act-laws (the latest
;;; citation since batch 8 moved the vector-group bricks there; before that, the latest
;;; citation: nvs-act-in-vec, nvs-act-collect, nvs-act-unital, nvs-act-scale-assoc,
;;; nvs-act-zero, nvs-vadd-assoc, nvs-scal-carr, nvs-scal-one) and BEFORE
;;; theorem-library/hahn-banach-proof, which asserts hb-extend-construct and
;;; cites it at :116.  That window exists only because nvs-module-view and
;;; nvs-act-laws were moved above hahn-banach-proof on 2026-09-19; the slot
;;; beside theorem-library/rake-hb-gap is the natural one.  Other floors:
;;; rake-algebra (span-add-one-membership), op-typing (nvs-vadd-in-vec),
;;; subset-lemmas (subset-mem-fwd), rake-setoid (vec-is-set), binary-minus-laws
;;; (rr-sub-in-rr), fun-apply-type-proof, equality-basics; the submodule
;;; projections (finite-dimensional.scm) are definitional and cost no bill.
;;; No late-loading tactic is used (no contra / prep / ineq-supply).
;;;
;;; THIS FILE MUST LOAD BEFORE theorem-library/rake-line-functional, which cites
;;; hbx-span-mem-eq and hbx-value.  The two files are one assignment and are
;;; wired together.  (Until batch 8 it also cited six vector-group lemmas from
;;; here; those are now nvs-act-laws.scm's and no longer constrain the pair.)
;;;
;;; WHAT THE INTEGRATOR RETIRES: theorem-library/hahn-banach-proof.scm:44-65
;;; (the add-to-pss / warrant! / topic! block for hb-extend-construct).
;;;
;;; The `hbx-' theorems are auxiliary.  The eleven vector-group ones were facts
;;; about a normed vector space, not about this proof; batch 8 promoted them to
;;; theorem-library/nvs-act-laws.scm, which is now their one home.
;;;
;;; Helper prefix `r8h-'; every helper is file-local.

(define r8h-nvs '(IS-NORMED-VECTOR-SPACE m))

(define (r8h-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8h-nvs)
  (dk-split-all!))

(define (r8h-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-hb-extend-construct: proof did not close" name
             (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

(define (r8h-core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (r8h-core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (r8h-core (caddr f)))
        (#t f)))

(define (r8h-law find what) (dk-pick (lambda (f) (find (r8h-core f))) what))

(define (r8h-refl-or-ass!)
  (let ((h (dk-goal)))
    (if (and (eq? (car h) '=) (equal? (cadr h) (caddr h))) (rfl) (ass))))

;;; MOVED 2026-09-19 (rake batch 8, assignment 8-K1) to
;;; theorem-library/nvs-act-laws.scm, which is now the ONE home of the normed-
;;; vector-space group and action laws (and nvs-norm-laws.scm of the norm laws):
;;;
;;;   hbx-vzero-in       -> nvs-vzero-in-vec
;;;   hbx-vneg-in        -> nvs-vneg-in-vec
;;;   hbx-vzero-left     -> nvs-vzero-left        (alpha-equivalent; dropped)
;;;   hbx-vneg-left      -> nvs-vneg-left
;;;   hbx-vadd-comm      -> nvs-vadd-comm         (alpha-equivalent; dropped)
;;;   hbx-act-distrib-c  -> nvs-act-distrib-vec   (alpha-equivalent; dropped)
;;;   hbx-act-distrib    -> nvs-act-distrib-vec-rr
;;;   hbx-act-one        -> nvs-one-act
;;;   hbx-act-sum        -> nvs-act-add-scalars   (alpha-equivalent; dropped)
;;;   hbx-vadd-cancel    -> nvs-vadd-cancel
;;;   hbx-vadd-cancel-right -> nvs-vadd-cancel-right
;;; The proofs went over verbatim; nothing here changed but the citations.
;;; The originals are archive/2026-09-19-batch8/.


;;; `ineq' wants 1-based assumption indices; name the premises by FORMULA.
(define (r8h-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r8h-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (r8h-ineq! . forms) (apply ineq (map r8h-idx forms)))

;;; =====================================================================
;;; (2)  s and SPAN-ADD-ONE(m,s,v): membership, in and out.
;;; =====================================================================

;;; THE LUTINS GUARD.  Without (IS-NORMED-VECTOR-SPACE m) the term (VEC m) is
;;; not certified DEFINED, so instantiating subset-mem-fwd at it owes the side
;;; sequent `vec(m) = vec(m)' -- an owed leaf with the parent's context, which
;;; nothing here can close (the same trap good-sub-in-power records).  Every use
;;; site has the structure hypothesis, so the guard costs nothing.
(sp (make-wff
     (forall-guarded '(m s p_)
       '((IS-NORMED-VECTOR-SPACE m) (IS-SUBMODULE m s) (IN p_ s))
       '(IN p_ (VEC m)))))
(dk-peel!)
(fact 'submodule-subset 'm 's)
(fact 'subset-mem-fwd 's '(VEC m) 'p_)
(ass)
(r8h-check! 'hbx-s-in-vec)

(sp (make-wff
 '(FORALL m
    (FORALL s
      (FORALL v
        (FORALL w_
          (IMPLIES (IN w_ (SPAN-ADD-ONE m s v)) (IN w_ (VEC m)))))))))
(dk-peel!)
(fact 'span-add-one-membership 'm 's 'v 'w_)
(prop)
(r8h-check! 'hbx-span-in-vec)

(sp (make-wff
 '(FORALL m
    (FORALL s
      (FORALL v
        (FORALL w_
          (IMPLIES (IN w_ (SPAN-ADD-ONE m s v))
            (FORSOME y_
              (AND (IN y_ s)
                   (FORSOME r_ (AND (IN r_ RR)
                                    (= w_ ((VADD m) y_ ((ACT m) r_ v))))))))))))))
(dk-peel!)
(fact 'span-add-one-membership 'm 's 'v 'w_)
(prop)
(r8h-check! 'hbx-span-decomp)

(sp (make-wff
     (forall-guarded '(m s v w_ p_ c_)
       '((IS-NORMED-VECTOR-SPACE m) (IS-SUBMODULE m s) (IN v (VEC m))
         (IN p_ s) (IN c_ RR) (= w_ ((VADD m) p_ ((ACT m) c_ v))))
       '(IN w_ (SPAN-ADD-ONE m s v)))))
(dk-peel!)
(fact 'hbx-s-in-vec 'm 's 'p_)
(fact 'nvs-act-in-vec 'm 'c_ 'v)
(fact 'nvs-vadd-in-vec 'm 'p_ '((ACT m) c_ v))
(have! '(IN w_ (VEC m))
       (lambda () (subst '(= w_ ((VADD m) p_ ((ACT m) c_ v)))) (ass)))
(fact 'span-add-one-membership 'm 's 'v 'w_)
(have! '(AND (IN w_ (VEC m))
             (FORSOME y_ (AND (IN y_ s)
                              (FORSOME r_ (AND (IN r_ RR)
                                               (= w_ ((VADD m) y_ ((ACT m) r_ v))))))))
       (lambda ()
         (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME)
                (begin (ew 'p_)
                       (dk-conj-close!
                        (lambda ()
                          (if (eq? (car (dk-goal)) 'FORSOME)
                              (begin (ew 'c_) (dk-conj-close! (lambda () (ass))))
                              (ass)))))
                (ass))))))
(prop)
(r8h-check! 'hbx-span-mem-eq)


;;; =====================================================================
;;; (3)  THE DECOMPOSITION IS UNIQUE.  This is the content of the leaf: with
;;; v outside s, p1 + c1.v = p2 + c2.v forces c1 = c2 and p1 = p2.  If c1 /= c2
;;; then (c1-c2).v = (-p1) + p2 lies in s, and v = (1/(c1-c2)).((c1-c2).v) lies
;;; in s with it -- against the hypothesis.
;;; =====================================================================

(sp (make-wff
     (forall-guarded '(m s v p1_ c1_ p2_ c2_)
       '((IS-NORMED-VECTOR-SPACE m) (IS-SUBMODULE m s) (IN v (VEC m)) (NOT (IN v s))
         (IN p1_ s) (IN c1_ RR) (IN p2_ s) (IN c2_ RR)
         (= ((VADD m) p1_ ((ACT m) c1_ v)) ((VADD m) p2_ ((ACT m) c2_ v))))
       '(AND (= c1_ c2_) (= p1_ p2_)))))
(dk-peel!)
(fact 'hbx-s-in-vec 'm 's 'p1_)
(fact 'hbx-s-in-vec 'm 's 'p2_)
(fact 'nvs-act-in-vec 'm 'c1_ 'v)
(fact 'nvs-act-in-vec 'm 'c2_ 'v)
(fact 'rr-sub-in-rr 'c1_ 'c2_)
(fact 'nvs-act-in-vec 'm '(- c1_ c2_) 'v)
(fact 'nvs-vneg-in-vec 'm 'p1_)
(fact 'nvs-vadd-in-vec 'm 'p1_ '((ACT m) (- c1_ c2_) v))
(fact 'nvs-vadd-in-vec 'm '((VNEG m) p1_) 'p2_)
(use-em '(= c1_ c2_)
  ;; ---- equal coefficients: cancel c1.v on the right ----
  (lambda ()
    (have! '(= ((VADD m) p2_ ((ACT m) c2_ v)) ((VADD m) p2_ ((ACT m) c1_ v)))
           (lambda () (subst '(= c1_ c2_)) (rfl)))
    (fact 'eq-trans '((VADD m) p1_ ((ACT m) c1_ v))
                    '((VADD m) p2_ ((ACT m) c2_ v))
                    '((VADD m) p2_ ((ACT m) c1_ v)))
    (fact 'nvs-vadd-cancel-right 'm '((ACT m) c1_ v) 'p1_ 'p2_)
    (dk-conj-close! (lambda () (ass))))
  ;; ---- different coefficients: v would lie in s ----
  (lambda ()
    (use-em '(= (- c1_ c2_) 0)
      (lambda ()
        (have! '(= c1_ c2_)
               (lambda () (r8h-ineq! '(= (- c1_ c2_) 0) '(IN c1_ RR) '(IN c2_ RR))))
        (ai '(NOT (= c1_ c2_))))
      (lambda ()
        ;; p1 + ((c1-c2).v + c2.v) = p2 + c2.v
        (fact 'nvs-act-add-scalars 'm '(- c1_ c2_) 'c2_ 'v)
        (have! '(= (+ (- c1_ c2_) c2_) c1_) (lambda () (crs)))
        (have! '(= ((VADD m) p1_ ((VADD m) ((ACT m) (- c1_ c2_) v) ((ACT m) c2_ v)))
                   ((VADD m) p2_ ((ACT m) c2_ v)))
          (lambda ()
            (subst '(= ((VADD m) ((ACT m) (- c1_ c2_) v) ((ACT m) c2_ v))
                       ((ACT m) (+ (- c1_ c2_) c2_) v)))
            (subst '(= (+ (- c1_ c2_) c2_) c1_))
            (ass)))
        ;; reassociate and cancel c2.v: p1 + (c1-c2).v = p2
        (fact 'nvs-vadd-assoc 'm 'p1_ '((ACT m) (- c1_ c2_) v) '((ACT m) c2_ v))
        (have! '(= ((VADD m) ((VADD m) p1_ ((ACT m) (- c1_ c2_) v)) ((ACT m) c2_ v))
                   ((VADD m) p2_ ((ACT m) c2_ v)))
          (lambda ()
            (subst '(= ((VADD m) ((VADD m) p1_ ((ACT m) (- c1_ c2_) v)) ((ACT m) c2_ v))
                       ((VADD m) p1_ ((VADD m) ((ACT m) (- c1_ c2_) v) ((ACT m) c2_ v)))))
            (ass)))
        (fact 'nvs-vadd-cancel-right 'm '((ACT m) c2_ v)
              '((VADD m) p1_ ((ACT m) (- c1_ c2_) v)) 'p2_)
        ;; (c1-c2).v = (-p1) + p2, and that lies in s
        (fact 'nvs-vadd-assoc 'm '((VNEG m) p1_) 'p1_ '((ACT m) (- c1_ c2_) v))
        (fact 'nvs-vneg-left 'm 'p1_)
        (fact 'nvs-vzero-left 'm '((ACT m) (- c1_ c2_) v))
        (have! '(= ((ACT m) (- c1_ c2_) v) ((VADD m) ((VNEG m) p1_) p2_))
          (lambda ()
            (subst '(= p2_ ((VADD m) p1_ ((ACT m) (- c1_ c2_) v))))
            (subst '(= ((VADD m) ((VNEG m) p1_) ((VADD m) p1_ ((ACT m) (- c1_ c2_) v)))
                       ((VADD m) ((VADD m) ((VNEG m) p1_) p1_) ((ACT m) (- c1_ c2_) v))))
            (subst '(= ((VADD m) ((VNEG m) p1_) p1_) (VZERO m)))
            (subst '(= ((VADD m) (VZERO m) ((ACT m) (- c1_ c2_) v))
                       ((ACT m) (- c1_ c2_) v)))
            (rfl)))
        (fact 'submodule-vneg-closed 'm 's 'p1_)
        (fact 'submodule-vadd-closed 'm 's '((VNEG m) p1_) 'p2_)
        (have! '(IN ((ACT m) (- c1_ c2_) v) s)
          (lambda ()
            (subst '(= ((ACT m) (- c1_ c2_) v) ((VADD m) ((VNEG m) p1_) p2_)))
            (ass)))
        ;; v = (1/(c1-c2)).((c1-c2).v) lies in s too -- the contradiction
        (have! '(AND (IN (- c1_ c2_) RR) (NOT (= (- c1_ c2_) 0))))
        (fact 'rr-recip-closed '(- c1_ c2_))
        (fact 'rr-recip-inverse '(- c1_ c2_))
        (have! '(AND (IN (recip (- c1_ c2_)) RR) (IN (- c1_ c2_) RR)))
        (fact 'rr-mul-comm '(recip (- c1_ c2_)) '(- c1_ c2_))
        (fact 'eq-trans '(* (recip (- c1_ c2_)) (- c1_ c2_))
                        '(* (- c1_ c2_) (recip (- c1_ c2_))) 1)
        (fact 'nvs-act-scale-assoc 'm '(recip (- c1_ c2_)) '(- c1_ c2_) 'v)
        (fact 'nvs-one-act 'm 'v)
        (have! '(= ((ACT m) (recip (- c1_ c2_)) ((ACT m) (- c1_ c2_) v)) v)
          (lambda ()
            (subst '(= ((ACT m) (recip (- c1_ c2_)) ((ACT m) (- c1_ c2_) v))
                       ((ACT m) (* (recip (- c1_ c2_)) (- c1_ c2_)) v)))
            (subst '(= (* (recip (- c1_ c2_)) (- c1_ c2_)) 1))
            (ass)))
        (have! '(IN (recip (- c1_ c2_)) (CARR (SCAL m)))
               (lambda () (mac 'nvs-scal-carr) (ass)))
        (fact 'submodule-act-closed 'm 's '(recip (- c1_ c2_)) '((ACT m) (- c1_ c2_) v))
        (have! '(IN v s)
          (lambda ()
            (subst '(= v ((ACT m) (recip (- c1_ c2_)) ((ACT m) (- c1_ c2_) v))))
            (ass)))
        (ai '(NOT (IN v s)))))))
(r8h-check! 'hbx-decomp-unique)


;;; =====================================================================
;;; (4)  Rearrangement, and the three read-offs of f.
;;; =====================================================================

;;; (A+B) + (C+D) = (A+C) + (B+D)
(sp (make-wff
     (forall-guarded '(m aa_ bb_ cc_ dd_)
       '((IS-NORMED-VECTOR-SPACE m) (IN aa_ (VEC m)) (IN bb_ (VEC m))
         (IN cc_ (VEC m)) (IN dd_ (VEC m)))
       '(= ((VADD m) ((VADD m) aa_ bb_) ((VADD m) cc_ dd_))
           ((VADD m) ((VADD m) aa_ cc_) ((VADD m) bb_ dd_))))))
(dk-peel!)
(fact 'nvs-vadd-in-vec 'm 'bb_ 'cc_)
(fact 'nvs-vadd-in-vec 'm 'cc_ 'bb_)
(fact 'nvs-vadd-in-vec 'm 'bb_ 'dd_)
(fact 'nvs-vadd-in-vec 'm 'cc_ 'dd_)
(fact 'nvs-vadd-in-vec 'm 'aa_ 'bb_)
(fact 'nvs-vadd-in-vec 'm 'aa_ 'cc_)
(fact 'nvs-vadd-assoc 'm 'aa_ 'bb_ '((VADD m) cc_ dd_))
(fact 'nvs-vadd-assoc 'm 'bb_ 'cc_ 'dd_)
(fact 'nvs-vadd-comm 'm 'bb_ 'cc_)
(fact 'nvs-vadd-assoc 'm 'cc_ 'bb_ 'dd_)
(fact 'nvs-vadd-assoc 'm 'aa_ 'cc_ '((VADD m) bb_ dd_))
(subst '(= ((VADD m) ((VADD m) aa_ bb_) ((VADD m) cc_ dd_))
           ((VADD m) aa_ ((VADD m) bb_ ((VADD m) cc_ dd_)))))
(subst '(= ((VADD m) bb_ ((VADD m) cc_ dd_))
           ((VADD m) ((VADD m) bb_ cc_) dd_)))
(subst '(= ((VADD m) bb_ cc_) ((VADD m) cc_ bb_)))
(subst '(= ((VADD m) ((VADD m) cc_ bb_) dd_)
           ((VADD m) cc_ ((VADD m) bb_ dd_))))
(subst '(= ((VADD m) ((VADD m) aa_ cc_) ((VADD m) bb_ dd_))
           ((VADD m) aa_ ((VADD m) cc_ ((VADD m) bb_ dd_)))))
(rfl)
(r8h-check! 'hbx-vadd-exchange)

;;; (y1 + c1.v) + (y2 + c2.v) = (y1+y2) + (c1+c2).v
(sp (make-wff
     (forall-guarded '(m v y1_ c1_ y2_ c2_)
       '((IS-NORMED-VECTOR-SPACE m) (IN v (VEC m)) (IN y1_ (VEC m)) (IN c1_ RR)
         (IN y2_ (VEC m)) (IN c2_ RR))
       '(= ((VADD m) ((VADD m) y1_ ((ACT m) c1_ v)) ((VADD m) y2_ ((ACT m) c2_ v)))
           ((VADD m) ((VADD m) y1_ y2_) ((ACT m) (+ c1_ c2_) v))))))
(dk-peel!)
(fact 'nvs-act-in-vec 'm 'c1_ 'v)
(fact 'nvs-act-in-vec 'm 'c2_ 'v)
(fact 'hbx-vadd-exchange 'm 'y1_ '((ACT m) c1_ v) 'y2_ '((ACT m) c2_ v))
(fact 'nvs-act-add-scalars 'm 'c1_ 'c2_ 'v)
(subst '(= ((VADD m) ((VADD m) y1_ ((ACT m) c1_ v)) ((VADD m) y2_ ((ACT m) c2_ v)))
           ((VADD m) ((VADD m) y1_ y2_) ((VADD m) ((ACT m) c1_ v) ((ACT m) c2_ v)))))
(subst '(= ((VADD m) ((ACT m) c1_ v) ((ACT m) c2_ v)) ((ACT m) (+ c1_ c2_) v)))
(fact 'nvs-vadd-in-vec 'm 'y1_ 'y2_)
(have! '(AND (IN c1_ RR) (IN c2_ RR)))
(fact 'rr-add-closed 'c1_ 'c2_)
(fact 'nvs-act-in-vec 'm '(+ c1_ c2_) 'v)
(fact 'nvs-vadd-in-vec 'm '((VADD m) y1_ y2_) '((ACT m) (+ c1_ c2_) v))
(rfl)
(r8h-check! 'hbx-add-decomp)

;;; f is additive and homogeneous on s.  ("f(p) is a real" was proven here as
;;; `hbx-f-real'; REMOVED 2026-09-20, batch 11: it was alpha-equal to
;;; `hbg-linfun-app-real' (theorem-library/rake-hb-gap.scm), which loads before
;;; this file.  The nine citations below name that one.)

(sp (make-wff
     (forall-guarded '(m s f x_ y_)
       '((IS-LINEAR-FUNCTIONAL-ON m s f) (IN x_ s) (IN y_ s))
       '(= (f ((VADD m) x_ y_)) (+ (f x_) (f y_))))))
(dk-peel!)
(mac-h 'is-linear-functional-on (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "f linear on s"))
(dk-split-all!)
(let ((law (r8h-law (lambda (c) (and (pair? c) (eq? (car c) '=)
                                     (pair? (caddr c)) (eq? (car (caddr c)) '+)))
                    "the additivity law of f")))
  (dk-apply! law 'x_ 'y_)
  (ass))
(r8h-check! 'hbx-f-add)

(sp (make-wff
     (forall-guarded '(m s f r_ x_)
       '((IS-LINEAR-FUNCTIONAL-ON m s f) (IN r_ RR) (IN x_ s))
       '(= (f ((ACT m) r_ x_)) (* r_ (f x_))))))
(dk-peel!)
(mac-h 'is-linear-functional-on (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "f linear on s"))
(dk-split-all!)
(let ((law (r8h-law (lambda (c) (and (pair? c) (eq? (car c) '=)
                                     (pair? (caddr c)) (eq? (car (caddr c)) '*)))
                    "the homogeneity law of f")))
  (dk-apply! law 'r_ 'x_)
  (ass))
(r8h-check! 'hbx-f-act)


;;; =====================================================================
;;; (5)  THE DESCRIPTION DENOTES, and its value.
;;;
;;; HBX-BODY(u) = IOTA t. t in RR and (some p in s, c in RR with u = p + c.v and
;;; t = f(p) + c*alpha).  v outside s makes the decomposition unique
;;; (hbx-decomp-unique), so the description denotes at every point of
;;; SPAN-ADD-ONE(m,s,v) and its value is f(p) + c*alpha.
;;; =====================================================================

;;; THE BINDER NAMES ARE NOT FREE.  The description is substituted INTO the
;;; body of IS-LINEAR-FUNCTIONAL-ON, whose binders are x_, y_, r_, and into the
;;; statement's own `forall y_, r_' clause; a description binding `y_' would be
;;; capture-renamed there, after which no reconstruction of the term made here
;;; matches the one in the goal and every `subst' silently rewrites nothing
;;; (measured: four "eq-subst: equality not in context" warnings and a dead
;;; additivity lane).  pv_ / cv_ / tv_ appear in no predicate body in the tree.
(define (r8h-iota-of u)
  (list 'IOTA 'tv_
        (list 'AND '(IN tv_ RR)
              (list 'FORSOME 'pv_
                    (list 'AND '(IN pv_ s)
                          (list 'FORSOME 'cv_
                                (list 'AND '(IN cv_ RR)
                                      (list 'AND
                                            (list '= u '((VADD m) pv_ ((ACT m) cv_ v)))
                                            '(= tv_ (+ (f pv_) (* cv_ a_)))))))))))

;;; Skolemize a two-level decomposition existential; return (point coefficient).
(define (r8h-open-decomp! ex)
  (let* ((y (dk-skolem! ex))
         (inner (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORSOME)
                                           (memq y (free-vars fm))))
                         "the coefficient existential"))
         (q (dk-skolem! inner)))
    (list y q)))

;;; From (= u (p_ + c_.v)) and (= u (y + q.v)) in context: land c_ = q and p_ = y.
(define (r8h-same-decomp! u y q)
  (fact 'eq-sym u '((VADD m) p_ ((ACT m) c_ v)))
  (fact 'eq-trans '((VADD m) p_ ((ACT m) c_ v)) u
        (list '(VADD m) y (list '(ACT m) q 'v)))
  (dk-split! (dk-fact! 'hbx-decomp-unique 'm 's 'v 'p_ 'c_ y q)))

(sp (make-wff
     (forall-guarded '(m s f v a_ u_ p_ c_)
       '((IS-NORMED-VECTOR-SPACE m) (IS-SUBMODULE m s) (IS-LINEAR-FUNCTIONAL-ON m s f)
         (IN v (VEC m)) (NOT (IN v s)) (IN a_ RR) (IN p_ s) (IN c_ RR)
         (= u_ ((VADD m) p_ ((ACT m) c_ v))))
       (list '= (r8h-iota-of 'u_) '(+ (f p_) (* c_ a_))))))
(dk-peel!)
(fact 'hbg-linfun-app-real 'm 's 'f 'p_)
(have! '(AND (IN c_ RR) (IN a_ RR)))
(fact 'rr-mul-closed 'c_ 'a_)
(have! '(AND (IN (f p_) RR) (IN (* c_ a_) RR)))
(fact 'rr-add-closed '(f p_) '(* c_ a_))
(let ((r8h-io (cadr (dk-goal))))
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         ;; ---- existence and uniqueness ----
         (begin
           (ew '(+ (f p_) (* c_ a_)))
           (dk-conj-close!
            (lambda ()
              (let ((g (dk-goal)))
                (cond
                  ((eq? (car g) 'IN) (ass))
                  ((eq? (car g) 'FORSOME)
                   (ew 'p_)
                   (dk-conj-close!
                    (lambda ()
                      (if (eq? (car (dk-goal)) 'FORSOME)
                          (begin (ew 'c_) (dk-conj-close! r8h-refl-or-ass!))
                          (ass)))))
                  ((eq? (car g) 'FORALL)
                   (dk-peel!)
                   (dk-split-all!)
                   (let* ((tv (caddr (dk-goal)))
                          (yq (r8h-open-decomp!
                               (dk-pick (dk-head? 'FORSOME) "the other decomposition"))))
                     (r8h-same-decomp! 'u_ (car yq) (cadr yq))
                     (subst (list '= tv (list '+ (list 'f (car yq))
                                              (list '* (cadr yq) 'a_))))
                     (subst (list '= 'p_ (car yq)))
                     (subst (list '= 'c_ (cadr yq)))
                     (fact 'hbg-linfun-app-real 'm 's 'f (car yq))
                     (have! (list 'AND (list 'IN (cadr yq) 'RR) '(IN a_ RR)))
                     (fact 'rr-mul-closed (cadr yq) 'a_)
                     (have! (list 'AND (list 'IN (list 'f (car yq)) 'RR)
                                  (list 'IN (list '* (cadr yq) 'a_) 'RR)))
                     (fact 'rr-add-closed (list 'f (car yq)) (list '* (cadr yq) 'a_))
                     (rfl)))
                  (#t (error "rake-hb-extend-construct: unexpected exuniq conjunct"
                             (expression->string g))))))))
         ;; ---- the main branch ----
         (begin
           (dk-split-all!)
           (let ((yq (r8h-open-decomp!
                      (dk-pick (dk-head? 'FORSOME) "the granted decomposition"))))
             (r8h-same-decomp! 'u_ (car yq) (cadr yq))
             (subst (list '= r8h-io (list '+ (list 'f (car yq))
                                          (list '* (cadr yq) 'a_))))
             (subst (list '= 'p_ (car yq)))
             (subst (list '= 'c_ (cadr yq)))
             (fact 'hbg-linfun-app-real 'm 's 'f (car yq))
             (have! (list 'AND (list 'IN (cadr yq) 'RR) '(IN a_ RR)))
             (fact 'rr-mul-closed (cadr yq) 'a_)
             (have! (list 'AND (list 'IN (list 'f (car yq)) 'RR)
                          (list 'IN (list '* (cadr yq) 'a_) 'RR)))
             (fact 'rr-add-closed (list 'f (car yq)) (list '* (cadr yq) 'a_))
             (rfl)))))
   (dk-opened (lambda () (iota-d r8h-io)))))
(r8h-check! 'hbx-value)


;;; =====================================================================
;;; (6)  hb-extend-construct -- hahn-banach-proof.scm:44
;;; =====================================================================

(define r8h-span '(SPAN-ADD-ONE m s v))
(define r8h-g (list 'VNB-LAMBDA 'u_ r8h-span (r8h-iota-of 'u_)))

;; the eigenvariables a peel landed with a given type, in order
(define (r8h-landed-in landed cls)
  (map cadr (filter (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                      (equal? (caddr fm) cls)))
                    landed)))

;; decompose a point of the span: returns (point coefficient), with
;; (IN point s), (IN coefficient RR) and the decomposition equation landed.
(define (r8h-decompose! u)
  (r8h-open-decomp! (dk-fact! 'hbx-span-decomp 'm 's 'v u)))

(define (r8h-additive? g)
  (let ((c (r8h-core g))) (and (eq? (car c) '=) (pair? (caddr c)) (eq? (car (caddr c)) '+))))

(sp `(FORALL m (FORALL s (FORALL f (FORALL v (FORALL a_
     (IMPLIES ,(conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                 (IS-SUBMODULE m s)
                                 (IS-LINEAR-FUNCTIONAL-ON m s f)
                                 (IN v (VEC m))
                                 (NOT (IN v s))
                                 (IN a_ RR)))
       (FORSOME g_
         ,(conjuncts->and
            '((IS-LINEAR-FUNCTIONAL-ON m (SPAN-ADD-ONE m s v) g_)
              (EXTENDS-ON s g_ f)
              (FORALL y_ (IMPLIES (IN y_ s)
                (FORALL r_ (IMPLIES (IN r_ RR)
                  (= (g_ ((VADD m) y_ ((ACT m) r_ v)))
                     (+ (f y_) (* r_ a_)))))))))))))))))
(dk-peel!)
(dk-split-all!)
(fact 'vec-is-set 'm)
(fact 'rr-zero-in)

;;; ---- (A) g is a linear functional on s + RR.v ----
(have! (list 'IS-LINEAR-FUNCTIONAL-ON 'm r8h-span r8h-g)
  (lambda ()
    (mac 'IS-LINEAR-FUNCTIONAL-ON)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
           ;; the FUN typing
           ((eq? (car g) 'IN)
            (for-each
             (lambda (leaf)
               (dk-focus! leaf)
               (if (equal? (dk-goal) (list 'IN r8h-span 'SET))
                   (begin (mac 'SPAN-ADD-ONE) (sep-set) (ass))
                   (let* ((u (dk-di-var!))
                          (yq (r8h-decompose! u)))
                     (fact 'hbx-value 'm 's 'f 'v 'a_ u (car yq) (cadr yq))
                     (subst (list '= (r8h-iota-of u)
                                  (list '+ (list 'f (car yq)) (list '* (cadr yq) 'a_))))
                     (fact 'hbg-linfun-app-real 'm 's 'f (car yq))
                     (have! (list 'AND (list 'IN (cadr yq) 'RR) '(IN a_ RR)))
                     (fact 'rr-mul-closed (cadr yq) 'a_)
                     (have! (list 'AND (list 'IN (list 'f (car yq)) 'RR)
                                  (list 'IN (list '* (cadr yq) 'a_) 'RR)))
                     (fact 'rr-add-closed (list 'f (car yq)) (list '* (cadr yq) 'a_))
                     (ass))))
             (dk-opened (lambda () (lam-t)))))
           ;; additivity
           ((r8h-additive? g)
            (let* ((landed (dk-peel!))
                   (us (r8h-landed-in landed r8h-span))
                   (u1 (car us)) (u2 (cadr us))
                   (d1 (r8h-decompose! u1))
                   (d2 (r8h-decompose! u2))
                   (y1 (car d1)) (q1 (cadr d1))
                   (y2 (car d2)) (q2 (cadr d2))
                   (ysum (list '(VADD m) y1 y2))
                   (qsum (list '+ q1 q2))
                   (usum (list '(VADD m) u1 u2)))
              (fact 'hbx-s-in-vec 'm 's y1)
              (fact 'hbx-s-in-vec 'm 's y2)
              (have! (list 'AND (list 'IN q1 'RR) (list 'IN q2 'RR)))
              (fact 'rr-add-closed q1 q2)
              (fact 'submodule-vadd-closed 'm 's y1 y2)
              (have! (list '= usum (list '(VADD m) ysum (list '(ACT m) qsum 'v)))
                (lambda ()
                  (subst (list '= u1 (list '(VADD m) y1 (list '(ACT m) q1 'v))))
                  (subst (list '= u2 (list '(VADD m) y2 (list '(ACT m) q2 'v))))
                  (fact 'hbx-add-decomp 'm 'v y1 q1 y2 q2)
                  (ass)))
              (fact 'hbx-span-mem-eq 'm 's 'v usum ysum qsum)
              (lam-b)
              (fact 'hbx-value 'm 's 'f 'v 'a_ u1 y1 q1)
              (fact 'hbx-value 'm 's 'f 'v 'a_ u2 y2 q2)
              (fact 'hbx-value 'm 's 'f 'v 'a_ usum ysum qsum)
              (subst (list '= (r8h-iota-of usum)
                           (list '+ (list 'f ysum) (list '* qsum 'a_))))
              (subst (list '= (r8h-iota-of u1)
                           (list '+ (list 'f y1) (list '* q1 'a_))))
              (subst (list '= (r8h-iota-of u2)
                           (list '+ (list 'f y2) (list '* q2 'a_))))
              (fact 'hbx-f-add 'm 's 'f y1 y2)
              (subst (list '= (list 'f ysum) (list '+ (list 'f y1) (list 'f y2))))
              (fact 'hbg-linfun-app-real 'm 's 'f y1)
              (fact 'hbg-linfun-app-real 'm 's 'f y2)
              (crs)))
           ;; homogeneity
           (#t
            (let* ((landed (dk-peel!))
                   (r (car (r8h-landed-in landed 'RR)))
                   (u (car (r8h-landed-in landed r8h-span)))
                   (yq (r8h-decompose! u))
                   (y0 (car yq)) (q0 (cadr yq))
                   (ru (list '(ACT m) r u))
                   (ry (list '(ACT m) r y0))
                   (rq (list '* r q0)))
              (fact 'hbx-s-in-vec 'm 's y0)
              (fact 'nvs-act-in-vec 'm q0 'v)
              (have! (list 'AND (list 'IN r 'RR) (list 'IN q0 'RR)))
              (fact 'rr-mul-closed r q0)
              (have! (list 'IN r '(CARR (SCAL m))) (lambda () (mac 'nvs-scal-carr) (ass)))
              (fact 'submodule-act-closed 'm 's r y0)
              (have! (list '= ru (list '(VADD m) ry (list '(ACT m) rq 'v)))
                (lambda ()
                  (subst (list '= u (list '(VADD m) y0 (list '(ACT m) q0 'v))))
                  (fact 'nvs-act-distrib-vec-rr 'm r y0 (list '(ACT m) q0 'v))
                  (subst (list '= (list '(ACT m) r (list '(VADD m) y0 (list '(ACT m) q0 'v)))
                               (list '(VADD m) ry (list '(ACT m) r (list '(ACT m) q0 'v)))))
                  (fact 'nvs-act-scale-assoc 'm r q0 'v)
                  (subst (list '= (list '(ACT m) r (list '(ACT m) q0 'v))
                               (list '(ACT m) rq 'v)))
                  (fact 'nvs-act-in-vec 'm rq 'v)
                  (fact 'nvs-act-in-vec 'm r y0)
                  (fact 'nvs-vadd-in-vec 'm ry (list '(ACT m) rq 'v))
                  (rfl)))
              (fact 'hbx-span-mem-eq 'm 's 'v ru ry rq)
              (lam-b)
              (fact 'hbx-value 'm 's 'f 'v 'a_ u y0 q0)
              (fact 'hbx-value 'm 's 'f 'v 'a_ ru ry rq)
              (subst (list '= (r8h-iota-of ru)
                           (list '+ (list 'f ry) (list '* rq 'a_))))
              (subst (list '= (r8h-iota-of u)
                           (list '+ (list 'f y0) (list '* q0 'a_))))
              (fact 'hbx-f-act 'm 's 'f r y0)
              (subst (list '= (list 'f ry) (list '* r (list 'f y0))))
              (fact 'hbg-linfun-app-real 'm 's 'f y0)
              (crs)))))))))

;;; ---- (B) g extends f ----
(have! (list 'EXTENDS-ON 's r8h-g 'f)
  (lambda ()
    (mac 'EXTENDS-ON)
    (let* ((landed (dk-peel!))
           (x (car (r8h-landed-in landed 's))))
      (fact 'hbx-s-in-vec 'm 's x)
      (fact 'nvs-act-zero 'm 'v x)
      (fact 'eq-sym (list '(VADD m) x '((ACT m) 0 v)) x)
      (fact 'hbx-span-mem-eq 'm 's 'v x x 0)
      (lam-b)
      (fact 'hbx-value 'm 's 'f 'v 'a_ x x 0)
      (subst (list '= (r8h-iota-of x) (list '+ (list 'f x) '(* 0 a_))))
      (fact 'hbg-linfun-app-real 'm 's 'f x)
      (crs))))

;;; ---- (C) the value formula ----
(have! (list 'FORALL 'y_
             (list 'IMPLIES '(IN y_ s)
                   (list 'FORALL 'r_
                         (list 'IMPLIES '(IN r_ RR)
                               (list '= (list r8h-g '((VADD m) y_ ((ACT m) r_ v)))
                                     '(+ (f y_) (* r_ a_)))))))
  (lambda ()
    (dk-peel!)
    (fact 'hbx-s-in-vec 'm 's 'y_)
    (fact 'nvs-act-in-vec 'm 'r_ 'v)
    (fact 'nvs-vadd-in-vec 'm 'y_ '((ACT m) r_ v))
    (have! '(= ((VADD m) y_ ((ACT m) r_ v)) ((VADD m) y_ ((ACT m) r_ v)))
           (lambda () (rfl)))
    (fact 'hbx-span-mem-eq 'm 's 'v '((VADD m) y_ ((ACT m) r_ v)) 'y_ 'r_)
    (lam-b)
    (fact 'hbx-value 'm 's 'f 'v 'a_ '((VADD m) y_ ((ACT m) r_ v)) 'y_ 'r_)
    (ass)))

(ew r8h-g)
(dk-conj-close! (lambda () (ass)))
(r8h-check! 'hb-extend-construct)

