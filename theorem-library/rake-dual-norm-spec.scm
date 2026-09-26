;;; rake-dual-norm-spec.scm -- the DUAL-NORM / DUAL-NORM-ON descriptions DENOTE,
;;; and the corollaries that follow from them.  Rake batch 7, assignment 7-A.
;;; Helper prefix `r8a-'.
;;;
;;; STATUS OF THE SIX COROLLARIES: each is proven here with `(IS-NORMED-VECTOR-SPACE m)'
;;; added as a CURRIED first antecedent, and the two `-ON' forms with
;;; `(SUBSET s (VEC m))' beside it (good-sub-self needs no second one:
;;; IS-SUBMODULE gives it).  The UNGUARDED statements at the
;;; support sites are UNDERDETERMINED -- see the counterexample in the closing
;;; block.  Whether the guarded forms replace them is the user's call, so the
;;; citers are untouched and the new names carry the suffix `-nvs'.
;;;
;;; CONTENTS
;;;   rr-le-of-le-add-all-pos    a <= b + d for every d > 0  =>  a <= b
;;;   rr-recip-cancel-right      a = (a * recip n) * n          (n /= 0)
;;;   rr-mul-recip-cancel        a = (a * n) * recip n          (n /= 0)
;;;   linfun-is-linfun-on-vec    the whole-space predicate is the s := VEC(m) case
;;;   blf-is-blf-on-vec          ... and likewise for the bounded one
;;;   dual-norm-on-lub-exists    the least nonnegative bound EXISTS
;;;   dual-norm-on-lub-unique    ... and is unique
;;;   dual-norm-on-spec          hence DUAL-NORM-ON(m,s,f) satisfies its IOTA body
;;;   dual-norm-spec             the same for DUAL-NORM(m,f)
;;;   dual-norm-on-nonneg-nvs / dual-norm-on-le-bound-nvs
;;;   dual-norm-nonneg-nvs / dual-norm-is-bound-nvs / dual-norm-le-bound-nvs
;;;   good-sub-self-nvs
;;;
;;; THE MATHEMATICS.  DUAL-NORM-ON(m,s,f) is `IOTA c. c in RR and 0 <= c and
;;; (forall x in s. |f(x)| <= c ||x||) and (c <= every such bound)' -- the LEAST
;;; nonnegative bound.  The tree has no INF over RR, only SUP (rr-sup-in,
;;; rr-sup-upper, rr-sup-least; number-systems.scm, PRIMITIVE, so they cost no
;;; bill entry).  Rather than reflect the set of bounds through 0, this file
;;; takes the sup of the QUOTIENTS
;;;
;;;     A = { a in RR : a = 0, or a = |f(x)| * recip(||x||) for some x in s
;;;                                with ||x|| /= 0 }
;;;
;;; and puts M = SUP(A).  A is nonempty (0 is in it) and bounded above by any
;;; bound c of f (divide |f(x)| <= c||x|| by ||x|| > 0), so SUP(A) exists; M is a
;;; bound (multiply |f(x)|*recip(||x||) <= M by ||x|| >= 0, and the ||x|| = 0 case
;;; is |f(x)| <= c*0 = 0 = M*0); and M is least, because every bound bounds A.
;;; That is the whole proof, and it needs NO epsilon argument -- the brick
;;; `rr-le-of-le-add-all-pos' that the route in scratchpad/rhb/HB-TRIAGE.md calls
;;; for is proven here as asked, but the spec does not use it.
;;;
;;; CITATIONS, with 0-based load.scm positions:
;;;   theory (11): subset-def          structure-library/finite-dimensional (55):
;;;   submodule-subset (definitional)  structure-library/linear-functional (64):
;;;   the definitions themselves       number-systems (34, PRIMITIVE): rr-zero-in,
;;;   rr-mul-closed, rr-mul-comm, rr-mul-assoc, rr-one-mul, rr-recip-closed,
;;;   rr-recip-inverse, rr-leq-antisymmetric, rr-sup-in, rr-sup-upper,
;;;   rr-sup-least   theorem-library/equality-basics (146): neq-sym
;;;   binary-minus-laws (159): rr-sub-in-rr   fun-apply-type-proof (160):
;;;   fun-apply-type-c   rr-abs-basics (177): rr-abs-closed   pos-rr-bridges
;;;   (176): rr-pos-rr-in-rr   rr-recip-order (181): rr-recip-pos
;;;   rr-order-bundle (184): rr-le-scale-nonneg-right   rr-le-all-pos (185):
;;;   rr-le-all-pos-nonpos   subset-lemmas (191): subset-mem-fwd
;;;   discrete-space (203): subset-refl   op-typing (207): vnrm-real
;;;   rake-hb-leaves (502): vnrm-nonneg
;;; Tactics: interactive (134), driver-kit (138), prop (141).  No late tactic
;;; (no `contra', `prep', `ineq-supply').
;;;
;;; LOAD WINDOW [503, 504): lo = 503 is rake-hb-leaves (502) + 1, forced by
;;; `vnrm-nonneg'; hi = 504 is theorem-library/hahn-banach-proof, the first file
;;; that would cite these if the guarded forms are adopted.  Slot: immediately
;;; before "theorem-library/hahn-banach-proof".

;;; =====================================================================
;;; (0)  FILE-LOCAL DRIVER HELPERS
;;; =====================================================================

;;; 1-BASED index of a context formula, for `ineq' (premise indices are 1-based;
;;; a finder that returned #f would leave the premise list quietly short).
(define (r8a-at f)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "r8a-at: not in context" (expression->string f)))
          ((equal? (car as) f) i)
          (#t (loop (cdr as) (+ i 1))))))

;;; =====================================================================
;;; (1)  THE BRICK:  a <= b + d for every d > 0  =>  a <= b.
;;; `rr-le-all-pos-nonpos' (rr-le-all-pos.scm) at x := a - b, plus two `ineq's.
;;; No archimedean argument is involved.  Stated CURRIED.
;;; =====================================================================

(sp (make-wff
     '(FORALL a_ (IMPLIES (IN a_ RR)
        (FORALL b_ (IMPLIES (IN b_ RR)
          (IMPLIES (FORALL d_ (IMPLIES (POS-RR d_) (<= a_ (+ b_ d_))))
                   (<= a_ b_))))))))
(dk-peel!)
(fact 'rr-sub-in-rr 'a_ 'b_)                      ; a - b in RR
;; The binder is spelled `eps' because that is rr-le-all-pos-nonpos's own binder:
;; `fact' detaches an antecedent that is in context, and a rebuilt alpha-variant
;; is a different formula to `member'.
(have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (- a_ b_) eps)))
  (lambda ()
    (let* ((landed (dk-peel!))
           (v      (caddr (dk-goal))))
      (fact 'rr-pos-rr-in-rr v)
      (dk-apply! '(FORALL d_ (IMPLIES (POS-RR d_) (<= a_ (+ b_ d_)))) v)
      (ineq (r8a-at (list '<= 'a_ (list '+ 'b_ v)))
            (r8a-at (list 'IN v 'RR))
            (r8a-at '(IN a_ RR))
            (r8a-at '(IN b_ RR))))))
(fact 'rr-le-all-pos-nonpos '(- a_ b_))           ; a - b <= 0
(ineq (r8a-at '(<= (- a_ b_) 0))
      (r8a-at '(IN a_ RR))
      (r8a-at '(IN b_ RR)))
(qed 'rr-le-of-le-add-all-pos)
(topic! 'rr-le-of-le-add-all-pos 'inequalities)
(alias! 'rr-le-of-le-add-all-pos
        "a real below b + d for every positive d is below b")

;;; =====================================================================
;;; (2)  THE TWO CANCELLATIONS.  Oriented `a = <product>' because `subst'
;;; rewrites the goal in the direction of its ARGUMENT: the goal mentions `a',
;;; and what the driver wants there is the product back.
;;; =====================================================================

(sp (make-wff
     '(FORALL a_ (IMPLIES (IN a_ RR)
        (FORALL n_ (IMPLIES (IN n_ RR)
          (IMPLIES (NOT (= n_ 0))
                   (= a_ (* (* a_ (recip n_)) n_)))))))))
(dk-peel!)
(have! '(AND (IN n_ RR) (NOT (= n_ 0))))
(fact 'rr-recip-closed 'n_)
(have! '(AND (IN a_ RR) (AND (IN (recip n_) RR) (IN n_ RR))))
(fact 'rr-mul-assoc 'a_ '(recip n_) 'n_)
(have! '(AND (IN (recip n_) RR) (IN n_ RR)))
(fact 'rr-mul-comm '(recip n_) 'n_)
(fact 'rr-recip-inverse 'n_)
(fact 'rr-one-in)
(have! '(AND (IN a_ RR) (IN 1 RR)))
(fact 'rr-mul-comm 'a_ 1)
(fact 'rr-one-mul 'a_)
(subst '(= (* (* a_ (recip n_)) n_) (* a_ (* (recip n_) n_))))
(subst '(= (* (recip n_) n_) (* n_ (recip n_))))
(subst '(= (* n_ (recip n_)) 1))
(subst '(= (* a_ 1) (* 1 a_)))
(subst '(= (* 1 a_) a_))
(rfl)
(qed 'rr-recip-cancel-right)
(topic! 'rr-recip-cancel-right 'inequalities)

(sp (make-wff
     '(FORALL a_ (IMPLIES (IN a_ RR)
        (FORALL n_ (IMPLIES (IN n_ RR)
          (IMPLIES (NOT (= n_ 0))
                   (= a_ (* (* a_ n_) (recip n_))))))))))
(dk-peel!)
(have! '(AND (IN n_ RR) (NOT (= n_ 0))))
(fact 'rr-recip-closed 'n_)
(have! '(AND (IN a_ RR) (AND (IN n_ RR) (IN (recip n_) RR))))
(fact 'rr-mul-assoc 'a_ 'n_ '(recip n_))
(fact 'rr-recip-inverse 'n_)
(fact 'rr-one-in)
(have! '(AND (IN a_ RR) (IN 1 RR)))
(fact 'rr-mul-comm 'a_ 1)
(fact 'rr-one-mul 'a_)
(subst '(= (* (* a_ n_) (recip n_)) (* a_ (* n_ (recip n_)))))
(subst '(= (* n_ (recip n_)) 1))
(subst '(= (* a_ 1) (* 1 a_)))
(subst '(= (* 1 a_) a_))
(rfl)
(qed 'rr-mul-recip-cancel)
(topic! 'rr-mul-recip-cancel 'inequalities)

;;; =====================================================================
;;; (3)  THE WHOLE-SPACE PREDICATES ARE THE s := VEC(m) CASE.
;;; The bodies of IS-LINEAR-FUNCTIONAL(m,f) and IS-LINEAR-FUNCTIONAL-ON(m,VEC m,f)
;;; are the same S-expression, and likewise for the bounded pair; the converse
;;; direction (ON => plain) is `linfun-on-vec-is-linfun', rake-hb-leaves.scm.
;;; =====================================================================

(sp (make-wff
     '(FORALL m (FORALL f
        (IMPLIES (IS-LINEAR-FUNCTIONAL m f) (IS-LINEAR-FUNCTIONAL-ON m (VEC m) f))))))
(dk-peel!)
(mac-h 'is-linear-functional (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL) "the plain hypothesis"))
(mac 'is-linear-functional-on)
(ass)
(qed 'linfun-is-linfun-on-vec)
(topic! 'linfun-is-linfun-on-vec 'analysis)

(sp (make-wff
     '(FORALL m (FORALL f
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f)
                 (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m (VEC m) f))))))
(dk-peel!)
(mac-h 'is-bounded-linear-functional
       (dk-pick (dk-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) "the plain hypothesis"))
(dk-split-all!)
(fact 'linfun-is-linfun-on-vec 'm 'f)
(mac 'is-bounded-linear-functional-on)
(dk-conj-close! (lambda () (ass)))
(qed 'blf-is-blf-on-vec)
(topic! 'blf-is-blf-on-vec 'analysis)

;;; =====================================================================
;;; (4)  EXISTENCE OF THE LEAST NONNEGATIVE BOUND.
;;;
;;; The guards are `(IS-NORMED-VECTOR-SPACE m)' and `(SUBSET s (VEC m))', and
;;; they are used for EXACTLY one thing: that ||x|| is a NONNEGATIVE REAL for
;;; every x in s (vnrm-real, vnrm-nonneg).  Without that the claim is false --
;;; see the closing block.
;;; =====================================================================

;;; the IOTA body of DUAL-NORM-ON (structure-library/linear-functional.scm:79-88)
;;; at an arbitrary term, with the binders x_ and d_ spelled as they are there.
;;; DOM is `s' for DUAL-NORM-ON and `(VEC m)' for DUAL-NORM: the two IOTA bodies
;;; are the SAME S-expression under that substitution.
(define (r8a-ub dom t)
  (list 'FORALL 'x_
        (list 'IMPLIES (list 'IN 'x_ dom)
              (list '<= '(abs (f x_)) (list '* t '((VNRM m) x_))))))

(define (r8a-least dom t)
  (list 'FORALL 'd_
        (list 'IMPLIES (list 'AND '(IN d_ RR)
                             (list 'AND '(<= 0 d_) (r8a-ub dom 'd_)))
              (list '<= t 'd_))))

(define (r8a-body dom t)
  (list 'AND (list 'IN t 'RR)
        (list 'AND (list '<= 0 t)
              (list 'AND (r8a-ub dom t) (r8a-least dom t)))))

;;; A = { |f(x)| / ||x|| : x in s, ||x|| /= 0 } u {0}, as a SEP over RR.  The 0
;;; keeps A INHABITED, which rr-sup-in requires and which "s has a vector of
;;; nonzero norm" does not give.
;;; The inner binder is `wq_', NOT `x_': the eigenvariable the BOUND conjunct
;;; peels off is called `x_' (the statement's own binder), and a term built from
;;; it, placed beside A, makes x_ both free and bound -- whereupon
;;; capture-avoiding substitution RENAMES A's binder and the formula that lands
;;; is no longer `equal?' to the A this file computes with.  That cost one probe.
(define r8a-A
  '(SEP a_ RR
     (OR (= a_ 0)
         (FORSOME wq_ (AND (IN wq_ s)
                      (AND (NOT (= ((VNRM m) wq_) 0))
                           (= a_ (* (abs (f wq_)) (recip ((VNRM m) wq_))))))))))
(define r8a-sup (list 'SUP r8a-A))

;;; A `have!' that declines a claim already in context (the kit item CLAUDE.md
;;; lists as OWED): `have!' ERRORS on an alpha-duplicate, and these helpers are
;;; called on branches whose contexts differ.
(define (r8a-have! form . opt)
  (if (not (any-pred (lambda (h) (alpha-equiv? h form)) (dk-asms)))
      (if (pair? opt) (have! form (car opt)) (have! form))))

(define (r8a-mul-in! u v)
  (r8a-have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;;; the typings of a point of s and of its norm
(define (r8a-type-point! xv)
  (fact 'subset-mem-fwd 's '(VEC m) xv)
  (fact 'vnrm-real 'm xv)
  (fact 'vnrm-nonneg 'm xv)
  (fact 'fun-apply-type-c 'f 's 'RR xv)
  (fact 'rr-abs-closed (list 'f xv)))

;;; 0 <= nx, nx /= 0  =>  recip(nx) is a nonnegative real.  The strict form is
;;; rebuilt by `mac' rather than read off, and the nonstrict one is taken in a
;;; `have!' LANE because `mac-h' would consume the strict inequality.
(define (r8a-recip-pos! nx)
  (fact 'neq-sym nx 0)
  (r8a-have! (list '< 0 nx) (lambda () (mac '<) (from-context!)))
  (r8a-have! (list 'AND (list 'IN nx 'RR) (list 'NOT (list '= nx 0))))
  (fact 'rr-recip-closed nx)
  (fact 'rr-recip-pos nx)
  (r8a-have! (list '<= 0 (list 'recip nx))
             (lambda () (mac-h '< (list '< 0 (list 'recip nx)))
                        (dk-split-all!)
                        (ass))))

;;; EVERY bound of f bounds A: goal (RR-UPPER-BOUND A t), with (IN t RR),
;;; (<= 0 t) and the bound law UB-LAW = (FORALL x. x in s => |f x| <= t ||x||)
;;; in context.  Used twice -- at the boundedness witness, and at the competing
;;; bound of the leastness conjunct.
(define (r8a-upper-bound! t ub-law)
  (mac 'RR-UPPER-BOUND)
  (both!
   (lambda () (ass))
   (lambda ()
     (dk-peel!)
     (let* ((v    (cadr (dk-goal)))
            (cnd  (car (filter (dk-head? 'OR)
                               (dk-landed (lambda () (sep-me (list 'IN v r8a-A))))))))
       (use-cases (list (list '= v 0) (caddr cnd))
         ;; a = 0
         (lambda () (subst (list '= v 0)) (ass))
         ;; a = |f(xv)| * recip(||xv||), with ||xv|| /= 0
         (lambda ()
           (let* ((xv (dk-skolem! (caddr cnd)))
                  (nx (list (list 'VNRM 'm) xv))
                  (fx (list 'abs (list 'f xv))))
             (r8a-type-point! xv)
             (r8a-recip-pos! nx)
             (dk-apply! ub-law xv)                    ; |f xv| <= t * ||xv||
             (r8a-mul-in! t nx)
             (fact 'rr-le-scale-nonneg-right fx (list '* t nx) (list 'recip nx))
             (fact 'rr-mul-recip-cancel t nx)         ; t = (t * ||xv||) * recip ||xv||
             (subst (list '= v (list '* fx (list 'recip nx))))
             (subst (list '= t (list '* (list '* t nx) (list 'recip nx))))
             (ass))))))))

;;; ---- the theorem -----------------------------------------------------

(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 's (list 'FORALL 'f
       (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(SUBSET s (VEC m))
           (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                 (list 'FORSOME 'c_ (r8a-body 's 'c_))))))))))
(dk-peel!)
(mac-h 'is-bounded-linear-functional-on
       (dk-pick (dk-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON) "the boundedness hypothesis"))
(dk-split-all!)
(mac-h 'is-linear-functional-on
       (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the linearity hypothesis"))
(dk-split-all!)
(define r8a-c0 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the boundedness witness")))
(define r8a-ub0
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (dk-contains? fm (list '* r8a-c0 (list '(VNRM m) (cadr fm))))))
           "the witness bound law"))

;; A is a set of reals, inhabited (0 is in it) and bounded above by c0.
(have! (list 'SUBSET r8a-A 'RR)
  (lambda ()
    (mac 'subset-def)
    (dk-peel!)
    (let ((v (cadr (dk-goal))))
      (sep-me (list 'IN v r8a-A))
      (ass))))
(have! (list 'IN 0 r8a-A)
  (lambda ()
    (in-sep! (lambda () (fact 'rr-zero-in) (ass))
             (lambda () (oi-l) (rfl)))))
(have! (list 'FORSOME 'x (list 'IN 'x r8a-A)) (lambda () (ew 0) (ass)))
(have! (list 'RR-BOUNDED-ABOVE r8a-A)
  (lambda () (mac 'RR-BOUNDED-ABOVE) (ew r8a-c0) (r8a-upper-bound! r8a-c0 r8a-ub0)))

(fact 'rr-sup-in r8a-A)                                  ; SUP A in RR
(fact 'rr-sup-upper r8a-A)                               ; RR-UPPER-BOUND(A, SUP A)
(define r8a-supub
  (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x r8a-A) (list '<= 'x r8a-sup))))
(have! r8a-supub
  (lambda () (mac-h 'RR-UPPER-BOUND (list 'RR-UPPER-BOUND r8a-A r8a-sup))
             (dk-split-all!)
             (ass)))
(have! (list '<= 0 r8a-sup) (lambda () (dk-apply! r8a-supub 0) (ass)))

;; the four conjuncts at SUP A
(ew r8a-sup)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((not (eq? (car g) 'FORALL)) (ass))
       ;; the LEASTNESS conjunct -- its guard is a conjunction
       ((eq? (car (cadr (caddr g))) 'AND)
        (dk-peel!)
        (dk-split-all!)
        (let ((dv (caddr (dk-goal))))
          (r8a-have! (list 'RR-UPPER-BOUND r8a-A dv)
                     (lambda () (r8a-upper-bound! dv (r8a-ub 's dv))))
          (fact 'rr-sup-least r8a-A dv)
          (ass)))
       ;; the BOUND conjunct -- |f x| <= SUP(A) * ||x|| for x in s
       (#t
        (let* ((landed (dk-peel!))
               (mem (car (filter (lambda (fm)
                                   (and (pair? fm) (eq? (car fm) 'IN) (equal? (caddr fm) 's)))
                                 landed)))
               (xv (cadr mem))
               (nx (list (list 'VNRM 'm) xv))
               (fx (list 'abs (list 'f xv))))
          (r8a-type-point! xv)
          (dk-apply! r8a-ub0 xv)                         ; |f xv| <= c0 * ||xv||
          (r8a-mul-in! r8a-c0 nx)
          (r8a-mul-in! r8a-sup nx)
          (use-em (list '= nx 0)
            ;; ||xv|| = 0: both products vanish and |f xv| <= 0
            (lambda ()
              (r8a-have! (list '= (list '* r8a-c0 nx) 0)
                         (lambda () (subst (list '= nx 0)) (fact 'rr-mul-zero r8a-c0) (ass)))
              (r8a-have! (list '= (list '* r8a-sup nx) 0)
                         (lambda () (subst (list '= nx 0)) (fact 'rr-mul-zero r8a-sup) (ass)))
              (ineq (r8a-at (list '<= fx (list '* r8a-c0 nx)))
                    (r8a-at (list '= (list '* r8a-c0 nx) 0))
                    (r8a-at (list '= (list '* r8a-sup nx) 0))
                    (r8a-at (list 'IN (list '* r8a-c0 nx) 'RR))
                    (r8a-at (list 'IN (list '* r8a-sup nx) 'RR))
                    (r8a-at (list 'IN fx 'RR))))
            ;; ||xv|| /= 0: the quotient is a member of A, so it is <= SUP A
            (lambda ()
              (r8a-recip-pos! nx)
              (let ((q (list '* fx (list 'recip nx))))
                (r8a-mul-in! fx (list 'recip nx))
                (r8a-have! (list 'IN q r8a-A)
                  (lambda ()
                    (in-sep! (lambda () (ass))
                             (lambda () (oi-r) (ew xv)
                                        (dk-conj-close!
                                         (lambda () (if (eq? (car (dk-goal)) '=) (rfl) (ass))))))))
                (dk-apply! r8a-supub q)                  ; q <= SUP A
                (fact 'rr-le-scale-nonneg-right q r8a-sup nx)
                (fact 'rr-recip-cancel-right fx nx)      ; |f xv| = q * ||xv||
                (subst (list '= fx (list '* q nx)))
                (ass))))))))))
(qed 'dual-norm-on-lub-exists)
(topic! 'dual-norm-on-lub-exists 'analysis)
(alias! 'dual-norm-on-lub-exists
        "a bounded functional on a subspace has a least nonnegative bound")

;;; =====================================================================
;;; (5)  UNIQUENESS.  Two least nonnegative bounds are mutually <=.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 's (list 'FORALL 'f
       (list 'FORALL 'c1_ (list 'FORALL 'c2_
         (list 'IMPLIES (r8a-body 's 'c1_)
               (list 'IMPLIES (r8a-body 's 'c2_) '(= c1_ c2_))))))))))
(dk-peel!)
(dk-split-all!)
(have! (list 'AND '(IN c2_ RR) (list 'AND '(<= 0 c2_) (r8a-ub 's 'c2_))))
(dk-apply! (r8a-least 's 'c1_) 'c2_)                  ; c1 <= c2
(have! (list 'AND '(IN c1_ RR) (list 'AND '(<= 0 c1_) (r8a-ub 's 'c1_))))
(dk-apply! (r8a-least 's 'c2_) 'c1_)                  ; c2 <= c1
(have! '(AND (IN c1_ RR) (IN c2_ RR)))
(have! '(AND (<= c1_ c2_) (<= c2_ c1_)))
(fact 'rr-leq-antisymmetric 'c1_ 'c2_)
(ass)
(qed 'dual-norm-on-lub-unique)
(topic! 'dual-norm-on-lub-unique 'analysis)

;;; =====================================================================
;;; (6)  THE DESCRIPTIONS DENOTE.  `iota-d' posts existence-and-uniqueness and
;;; grants the defining property -- the direction a definition wants.  The model
;;; is theorem-library/rake-esup-defined.scm, section (4).
;;; =====================================================================

;;; the existence-and-uniqueness lane, over the domain DOM
(define (r8a-exuniq! dom)
  (let* ((ex (dk-fact! 'dual-norm-on-lub-exists 'm dom 'f))
         (w  (dk-skolem! ex)))
    (dk-split-all!)
    (ew w)
    (for-each
     (lambda (k)
       (dk-focus! k)
       (if (eq? (car (dk-goal)) 'FORALL)
           (begin
             (dk-peel!)
             (let ((y (caddr (dk-goal))))
               (r8a-have! (r8a-body dom w))
               (fact 'dual-norm-on-lub-unique 'm dom 'f w y)
               (ass)))
           (dk-conj-close! (lambda () (ass)))))
     (dk-opened (lambda () (di))))))

(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 's (list 'FORALL 'f
       (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(SUBSET s (VEC m))
           (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                 (r8a-body 's '(DUAL-NORM-ON m s f))))))))))
(dk-peel!)
(mac 'DUAL-NORM-ON)
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (car (dk-goal)) 'FORSOME) (r8a-exuniq! 's) (ass)))
 (dk-opened (lambda () (iota-d (cadr (cadr (dk-goal)))))))
(qed 'dual-norm-on-spec)
(topic! 'dual-norm-on-spec 'analysis)
(alias! 'dual-norm-on-spec
        "the operator norm on a subspace is the least nonnegative bound")

;;; The whole-space description.  Its IOTA body is the s := VEC(m) instance of
;;; the one above, so the two lemmas of (4) and (5) serve unchanged.
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f
       (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m f)
               (r8a-body '(VEC m) '(DUAL-NORM m f))))))))
(dk-peel!)
(fact 'blf-is-blf-on-vec 'm 'f)
(fact 'subset-refl '(VEC m))
(mac 'DUAL-NORM)
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (car (dk-goal)) 'FORSOME) (r8a-exuniq! '(VEC m)) (ass)))
 (dk-opened (lambda () (iota-d (cadr (cadr (dk-goal)))))))
(qed 'dual-norm-spec)
(topic! 'dual-norm-spec 'analysis)
(alias! 'dual-norm-spec "the operator norm is the least nonnegative bound")

;;; =====================================================================
;;; (7)  THE SIX COROLLARIES, GUARDED.  Each statement is the support site's,
;;; character for character, with `(IS-NORMED-VECTOR-SPACE m)' -- and, where the
;;; subspace is not already a submodule, `(SUBSET s (VEC m))' -- prefixed as
;;; CURRIED antecedents.  See the closing block for why the unguarded forms
;;; cannot be proven.
;;; =====================================================================

;;; the bound / leastness conjuncts over an arbitrary functional symbol
(define (r8a-ub2 fn dom t)
  (list 'FORALL 'x_
        (list 'IMPLIES (list 'IN 'x_ dom)
              (list '<= (list 'abs (list fn 'x_)) (list '* t (list '(VNRM m) 'x_))))))
(define (r8a-least2 fn dom t)
  (list 'FORALL 'd_
        (list 'IMPLIES (list 'AND '(IN d_ RR)
                             (list 'AND '(<= 0 d_) (r8a-ub2 fn dom 'd_)))
              (list '<= t 'd_))))

;;; ---- dual-norm-on-nonneg  (hahn-banach-full-proof.scm:39) ------------
(sp (make-wff
     '(FORALL m (FORALL s (FORALL f
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (SUBSET s (VEC m))
          (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
            (AND (IN (DUAL-NORM-ON m s f) RR) (<= 0 (DUAL-NORM-ON m s f)))))))))))
(dk-peel!)
(fact 'dual-norm-on-spec 'm 's 'f)
(dk-split-all!)
(dk-conj-close! (lambda () (ass)))
(qed 'dual-norm-on-nonneg-nvs)
(topic! 'dual-norm-on-nonneg-nvs 'analysis)

;;; ---- dual-norm-on-le-bound  (hahn-banach-full-proof.scm:49) ----------
(sp (make-wff
     '(FORALL m (FORALL s (FORALL g (FORALL c
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (SUBSET s (VEC m))
          (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m s g)
           (IMPLIES (IN c RR)
            (IMPLIES (<= 0 c)
             (IMPLIES (FORALL w_ (IMPLIES (IN w_ s)
                        (<= (abs (g w_)) (* c ((VNRM m) w_)))))
               (<= (DUAL-NORM-ON m s g) c)))))))))))))
(dk-peel!)
;; the explicit bound IS boundedness; `ass' is alpha-aware, so the w_ / x_
;; difference in the two spellings of the bound law costs nothing.
(have! '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s g)
  (lambda () (mac 'is-bounded-linear-functional-on)
             (both! (lambda () (ass))
                    (lambda () (ew 'c) (dk-conj-close! (lambda () (ass)))))))
(fact 'dual-norm-on-spec 'm 's 'g)
(dk-split-all!)
(have! (list 'AND '(IN c RR) (list 'AND '(<= 0 c) (r8a-ub2 'g 's 'c))))
(dk-apply! (r8a-least2 'g 's '(DUAL-NORM-ON m s g)) 'c)
(ass)
(qed 'dual-norm-on-le-bound-nvs)
(topic! 'dual-norm-on-le-bound-nvs 'analysis)

;;; ---- dual-norm-on-is-bound  (NO support site: the tree had only the ----
;;; whole-space dual-norm-is-bound.  Added by the integrator on 2026-09-19 at
;;; the request of rake-hb-gap.scm, which needs "DUAL-NORM-ON(m,s,f) IS a
;;; bound on s" and had to reach it through good-sub-self.) ---------------
(sp (make-wff
     '(FORALL m (FORALL s (FORALL f (FORALL x
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (SUBSET s (VEC m))
          (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
           (IMPLIES (IN x s)
             (<= (abs (f x)) (* (DUAL-NORM-ON m s f) ((VNRM m) x)))))))))))))
(dk-peel!)
(fact 'dual-norm-on-spec 'm 's 'f)
(dk-split-all!)
(dk-apply! (r8a-ub2 'f 's '(DUAL-NORM-ON m s f)) 'x)
(ass)
(qed 'dual-norm-on-is-bound-nvs)
(topic! 'dual-norm-on-is-bound-nvs 'analysis)

;;; ---- dual-norm-nonneg  (norm-as-sup-proof.scm:60) --------------------
(sp (make-wff
     '(FORALL m (FORALL f
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f)
           (AND (IN (DUAL-NORM m f) RR) (<= 0 (DUAL-NORM m f)))))))))
(dk-peel!)
(fact 'dual-norm-spec 'm 'f)
(dk-split-all!)
(dk-conj-close! (lambda () (ass)))
(qed 'dual-norm-nonneg-nvs)
(topic! 'dual-norm-nonneg-nvs 'analysis)

;;; ---- dual-norm-is-bound  (norm-as-sup-proof.scm:50) ------------------
(sp (make-wff
     '(FORALL m (FORALL f (FORALL x
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m f)
          (IMPLIES (IN x (VEC m))
            (<= (abs (f x)) (* (DUAL-NORM m f) ((VNRM m) x)))))))))))
(dk-peel!)
(fact 'dual-norm-spec 'm 'f)
(dk-split-all!)
(dk-apply! (r8a-ub2 'f '(VEC m) '(DUAL-NORM m f)) 'x)
(ass)
(qed 'dual-norm-is-bound-nvs)
(topic! 'dual-norm-is-bound-nvs 'analysis)

;;; ---- dual-norm-le-bound  (norm-as-sup-proof.scm:78) -----------------
(sp (make-wff
     '(FORALL m (FORALL f (FORALL c
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-LINEAR-FUNCTIONAL m f)
          (IMPLIES (IN c RR)
           (IMPLIES (<= 0 c)
            (IMPLIES (FORALL w_ (IMPLIES (IN w_ (VEC m))
                       (<= (abs (f w_)) (* c ((VNRM m) w_)))))
              (<= (DUAL-NORM m f) c)))))))))))
(dk-peel!)
(have! '(IS-BOUNDED-LINEAR-FUNCTIONAL m f)
  (lambda () (mac 'is-bounded-linear-functional)
             (both! (lambda () (ass))
                    (lambda () (ew 'c) (dk-conj-close! (lambda () (ass)))))))
(fact 'dual-norm-spec 'm 'f)
(dk-split-all!)
(have! (list 'AND '(IN c RR) (list 'AND '(<= 0 c) (r8a-ub2 'f '(VEC m) 'c))))
(dk-apply! (r8a-least2 'f '(VEC m) '(DUAL-NORM m f)) 'c)
(ass)
(qed 'dual-norm-le-bound-nvs)
(topic! 'dual-norm-le-bound-nvs 'analysis)

;;; ---- good-sub-self  (noetherian-maximal-proof.scm:228) ---------------
;;; s is reachable from itself: f is a norm-preserving extension of f to s.
;;; No `(SUBSET s (VEC m))' antecedent is needed -- IS-SUBMODULE gives it.
(sp (make-wff
     '(FORALL m (FORALL s (FORALL f
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-SUBMODULE m s)
          (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
            (GOOD-SUB m s f s)))))))))
(dk-peel!)
(fact 'submodule-subset 'm 's)
(fact 'dual-norm-on-spec 'm 's 'f)
(dk-split-all!)
;; both reads are taken in LANES: `mac-h' consumes, and the two predicates are
;; still wanted -- IS-LINEAR-FUNCTIONAL-ON as a conjunct of NPE.
(have! '(IS-LINEAR-FUNCTIONAL-ON m s f)
  (lambda () (mac-h 'is-bounded-linear-functional-on
                    '(IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f))
             (dk-split-all!)
             (ass)))
(have! '(IN f (FUN s RR))
  (lambda () (mac-h 'is-linear-functional-on '(IS-LINEAR-FUNCTIONAL-ON m s f))
             (dk-split-all!)
             (ass)))
(mac 'GOOD-SUB)
(ew 'f)
(mac 'NPE)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'SUBSET) (fact 'subset-refl 's) (ass))
       ((eq? (car g) 'EXTENDS-ON)
        (mac 'EXTENDS-ON)
        (let* ((landed (dk-peel!))
               (xv (cadr (car (filter (lambda (fm)
                                        (and (pair? fm) (eq? (car fm) 'IN)
                                             (equal? (caddr fm) 's)))
                                      landed)))))
          (fact 'fun-apply-type-c 'f 's 'RR xv)
          (rfl)))
       (#t (ass))))))
(qed 'good-sub-self-nvs)
(topic! 'good-sub-self-nvs 'analysis)

;;; =====================================================================
;;; (8)  WHY THE UNGUARDED STATEMENTS CANNOT BE PROVEN.
;;;
;;; The six supports are guarded only by boundedness (or, for the two
;;; `-le-bound' forms, by linearity plus an explicit bound, which IS
;;; boundedness).  Nothing in IS-BOUNDED-LINEAR-FUNCTIONAL-ON(m,s,f) constrains
;;; the NORM: m is an arbitrary set, (VNRM m) is an arbitrary slot of it, and
;;; `*' is TOTAL and unaxiomatised off RR -- `(* x y)' is `bintimes(x,y)'
;;; (nary-times-2, unguarded), and the comment at
;;; structure-library/numeric-instances.scm:100 records that the bridge symbols
;;; are deliberately NOT asserted into any FUN class, so nothing makes the
;;; product undefined at a non-real argument either.  Every axiom about `*' and
;;; `<=' in number-systems.scm carries an `(IN _ RR)' guard.
;;;
;;; A COUNTERMODEL, then, for `dual-norm-on-nonneg' as stated at
;;; hahn-banach-full-proof.scm:39.  Let u be any set that is not a number, and
;;; interpret the product on RR x {u} by
;;;
;;;     c * u  =  1   if c is 2^-k for some k in NN
;;;     c * u  = -1   otherwise
;;;
;;; (a legitimate interpretation: no axiom mentions it).  Take
;;;
;;;     s = {p},  f = {<p,0>}  in FUN(s,RR),
;;;     (VADD m) and (ACT m) constant at p,  (VNRM m) = {<p,u>}.
;;;
;;; IS-LINEAR-FUNCTIONAL-ON(m,s,f) holds: f(VADD(p,p)) = f(p) = 0 = f(p)+f(p),
;;; and f(ACT(r,p)) = f(p) = 0 = r*0 for every real r.  f is BOUNDED: c = 1
;;; gives |f(p)| = 0 <= 1 = 1*u.  But the set of admissible bounds is
;;;
;;;     C = { c in RR : 0 <= c and 0 <= c*u } = { 1, 1/2, 1/4, ... },
;;;
;;; which has NO least element.  So no c satisfies the body of DUAL-NORM-ON's
;;; IOTA, the description does not denote, and `(IN (DUAL-NORM-ON m s f) RR)' is
;;; FALSE.  The same model refutes `dual-norm-on-le-bound' (at c = 1) and, with
;;; s := VEC(m), the three whole-space forms; `good-sub-self' fails through
;;; NPE's fifth conjunct, which measures g against DUAL-NORM-ON(m,s,f).
;;;
;;; WHAT THE GUARD COSTS THE CITERS.  Every citation site already carries
;;; `(IS-NORMED-VECTOR-SPACE m)'.  The extra `(SUBSET s (VEC m))' of the two
;;; `-ON' forms is one citation of `submodule-subset' at
;;; hahn-banach-full-proof.scm:195 and :201 (IS-SUBMODULE(m,t) is in context),
;;; immediate at norm-as-sup-proof.scm:164 (LINE is a SEP over VEC(m)), and two
;;; citations at hahn-banach-full-proof.scm:145, where s is known to be a
;;; subspace only through GOOD-SUB(m,s,f,t): SUBSET s t (NPE's second conjunct)
;;; and submodule-subset at t, then subset-trans.
;;;
;;; The minimal honest hypothesis is weaker than IS-NORMED-VECTOR-SPACE: all the
;;; proof uses is `forall x in s. (VNRM m)(x) in RR and 0 <= (VNRM m)(x)'.  It
;;; is stated here as NVS + SUBSET because that is what the citers hold.
;;;
;;; WHAT THE INTEGRATOR DOES, if the user adopts the guarded forms:
;;;   1. wire this file into load.scm immediately before
;;;      "theorem-library/hahn-banach-proof" (position 504);
;;;   2. retire the six supports --
;;;        dual-norm-on-nonneg   theorem-library/hahn-banach-full-proof.scm:39-46
;;;        dual-norm-on-le-bound theorem-library/hahn-banach-full-proof.scm:49-60
;;;        dual-norm-is-bound    theorem-library/norm-as-sup-proof.scm:50-57
;;;        dual-norm-nonneg      theorem-library/norm-as-sup-proof.scm:60-67
;;;        dual-norm-le-bound    theorem-library/norm-as-sup-proof.scm:78-89
;;;        good-sub-self         theorem-library/noetherian-maximal-proof.scm:228-234
;;;      and rename the citations (scratchpad/rename-sym.py) to the `-nvs'
;;;      names, supplying the SUBSET antecedent at the five `-ON' call sites
;;;      listed above;
;;;   3. or, if the user prefers the names unchanged, drop the `-nvs' suffix
;;;      here -- the statements are then NOT the ones at the sites, and the
;;;      difference is the added antecedents.
