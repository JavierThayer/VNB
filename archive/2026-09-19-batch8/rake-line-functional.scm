;;; rake-line-functional.scm -- line-functional-exists (theorem-library/
;;; norm-as-sup-proof.scm:43), rake batch 7, assignment 7-C.
;;;
;;;   m a real normed vector space, v in VEC(m)  =>  there is a bounded linear
;;;   functional f on the line RR.v with ||f||_{RR.v} <= 1 and f(v) = ||v||.
;;;
;;; THE CONSTRUCTION, and why there is no case split on v = 0.  The functional
;;; wanted is r.v |-> r||v||, and "the r such that u = r.v" is not a term: it is
;;; a DESCRIPTION, and for v = 0 it does not even denote (every r works).  What
;;; DOES denote for every v is the VALUE:
;;;
;;;   LFE-BODY(u) = IOTA t. t in RR and (some q in RR with u = q.v and t = q||v||)
;;;
;;; -- for v = 0 the coefficient is undetermined but ||v|| = 0, so t = 0 either
;;; way.  So the seed functional is ONE lambda,
;;;
;;;   f = VNB-LAMBDA u in LINE(m,v). LFE-BODY(u),
;;;
;;; with no case analysis anywhere below; the warrant's "for v=0 the zero
;;; functional serves" is subsumed.
;;;
;;; THE CONTENT is `lfe-coef-unique': q.v = q'.v  =>  q||v|| = q'||v||.  That is
;;; not a norm fact -- the norm cannot tell r.v from (-r).v -- it needs
;;; CANCELLATION in the vector group, which the tree did not have for a normed
;;; vector space.  `lfe-vadd-cancel' (x + z = x => z = 0) is proven here from the
;;; is-identity / has-inverses / is-associative conjuncts of
;;; IS-NORMED-VECTOR-SPACE, and is the one piece worth lifting out of this file:
;;; every "the decomposition is unique" argument in the Hahn-Banach arc
;;; (hb-extend-construct next) goes through it.
;;;
;;; THE BILL: `modulo 0'.  The conjunct `DUAL-NORM-ON(m, LINE(m,v), f) <= 1'
;;; is discharged by `dual-norm-on-le-bound-nvs' (theorem-library/
;;; rake-dual-norm-spec.scm, batch 7-A, itself modulo 0) -- the GUARDED form,
;;; not the asserted `dual-norm-on-le-bound' at hahn-banach-full-proof.scm:49,
;;; which 7-A reports as underdetermined.  The bound hypothesis it takes is
;;; proven here: |f(w)| = ||w|| on the line, exactly.
;;;
;;; THIS FILE MUST LOAD AFTER theorem-library/rake-hb-extend-construct, the
;;; other half of this assignment: six vector-group lemmas (hbx-vzero-in,
;;; hbx-vneg-in, hbx-vzero-left, hbx-vneg-left, hbx-act-one, hbx-act-sum) are
;;; proven there and cited here rather than proved twice.
;;;
;;; LOAD WINDOW: any slot after theorem-library/nvs-act-laws (the latest
;;; citation: nvs-scal-carr, nvs-scal-one, nvs-act-unital, nvs-act-in-vec,
;;; nvs-act-collect, nvs-vadd-assoc, nvs-act-scale-assoc) -- and after
;;; rake-dual-norm-spec and rake-hb-extend-construct, both of which sit there
;;; too -- and BEFORE theorem-library/norm-as-sup-proof, the ONLY citer of
;;; line-functional-exists (:142).  Other floors: rake-hb-leaves (vnrm-nonneg),
;;; op-typing (vnrm-real), rr-abs-basics (rr-abs-mult, rr-abs-of-nonneg,
;;; rr-abs-closed, rr-abs-zero), rr-order-basics (rr-no-zero-divisors),
;;; rake-setoid (vec-is-set), binary-minus-laws (rr-sub-in-rr),
;;; fun-apply-type-proof, equality-basics.  Recommended slot: immediately after
;;; rake-hb-extend-construct (beside rake-hb-gap), or anywhere up to
;;; norm-as-sup-proof.
;;; No late-loading tactic is used (no contra / prep / ineq-supply).
;;;
;;; WHAT THE INTEGRATOR RETIRES: theorem-library/norm-as-sup-proof.scm:43-53
;;; (the add-to-pss / warrant! / topic! block for line-functional-exists).
;;;
;;; The `lfe-' theorems are auxiliary and carry that prefix so that no two
;;; agents of this batch collide on a name; lfe-vadd-cancel, lfe-vnrm-homog and
;;; lfe-vnrm-vzero are facts about a normed vector space, not about this proof,
;;; and belong beside nvs-act-laws.scm's five when someone promotes them.
;;;
;;; Helper prefix `r8c-'; every helper is file-local.

(define r8c-nvs '(IS-NORMED-VECTOR-SPACE m))

(define (r8c-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8c-nvs)
  (dk-split-all!))

(define (r8c-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-line-functional: proof did not close" name
             (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;; the innermost consequent of a FORALL/IMPLIES tower
(define (r8c-core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (r8c-core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (r8c-core (caddr f)))
        (#t f)))

(define (r8c-law find what) (dk-pick (lambda (f) (find (r8c-core f))) what))

(define (r8c-in-head h)
  (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
                   (eq? (car (caddr f)) h))))

;; (IN r (CARR (SCAL m))) from (IN r RR) -- nvs-act-laws.scm's nal-scalar!
(define (r8c-scalar! r)
  (have! (list 'IN r '(CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

;;; =====================================================================
;;; (1)  LINE: the unfold equation and the membership iff.
;;; =====================================================================

(sp (make-wff '(FORALL m (FORALL v
   (== (LINE m v)
       (SEP y_ (VEC m)
         (FORSOME r_ (AND (IN r_ RR) (= y_ ((ACT m) r_ v))))))))))
(di) (mac 'LINE) (qrfl)
(r8c-check! 'lfe-line-unfold)

(sp (make-wff '(FORALL m (FORALL v (FORALL w_
   (IFF (IN w_ (LINE m v))
        (AND (IN w_ (VEC m))
             (FORSOME r_ (AND (IN r_ RR) (= w_ ((ACT m) r_ v)))))))))))
(di)
(let ((ls (dk-opened (lambda () (di)))))
  (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'AND)) ls))
  (mac-h 'lfe-line-unfold (dk-pick (r8c-in-head 'LINE) "w_ in LINE"))
  (sep-me (dk-pick (r8c-in-head 'SEP) "w_ in the SEP"))
  (dk-conj-close! (lambda () (ass)))
  (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'AND))) ls))
  (dk-split! (dk-pick (dk-head? 'AND) "the decomposition conjunction"))
  (mac 'LINE)
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi)))))
(r8c-check! 'lfe-line-membership)

;; w in LINE(m,v) is a vector.
(sp (make-wff '(FORALL m (FORALL v (FORALL w_
   (IMPLIES (IN w_ (LINE m v)) (IN w_ (VEC m))))))))
(dk-peel!)
(fact 'lfe-line-membership 'm 'v 'w_)
(prop)
(r8c-check! 'lfe-line-in-vec)

;; ... so the line is a subset of the vectors (the form dual-norm-on-le-bound-nvs
;; takes).
(sp (make-wff '(FORALL m (FORALL v (SUBSET (LINE m v) (VEC m))))))
(dk-peel!)
(mac 'subset-def)
(let ((r8c-w (dk-di-var!)))
  (fact 'lfe-line-in-vec 'm 'v r8c-w)
  (ass))
(r8c-check! 'lfe-line-subset)

;; w in LINE(m,v) has a real coefficient.
(sp (make-wff '(FORALL m (FORALL v (FORALL w_
   (IMPLIES (IN w_ (LINE m v))
     (FORSOME r_ (AND (IN r_ RR) (= w_ ((ACT m) r_ v))))))))))
(dk-peel!)
(fact 'lfe-line-membership 'm 'v 'w_)
(prop)
(r8c-check! 'lfe-line-coef)

;; ... and conversely.  Stated with the decomposition as a HYPOTHESIS rather
;; than with w_ := r_.v: every use site holds the equation and would otherwise
;; need a `subst' of it into the goal, which rewrites the v inside LINE(m,v) too.
(sp (make-wff '(FORALL m (FORALL v (FORALL w_ (FORALL r_
   (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
   (IMPLIES (IN r_ RR) (IMPLIES (= w_ ((ACT m) r_ v))
     (IN w_ (LINE m v))))))))))))
(dk-peel!)
(fact 'nvs-act-in-vec 'm 'r_ 'v)
(fact 'lfe-line-membership 'm 'v 'w_)
(have! '(IN w_ (VEC m))
       (lambda () (subst '(= w_ ((ACT m) r_ v))) (ass)))
(have! '(AND (IN w_ (VEC m))
             (FORSOME r_ (AND (IN r_ RR) (= w_ ((ACT m) r_ v)))))
       (lambda ()
         (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME)
                (begin (ew 'r_) (dk-conj-close! (lambda () (ass))))
                (ass))))))
(prop)
(r8c-check! 'lfe-line-mem-eq)

;;; =====================================================================
;;; (2)  Projections of IS-NORMED-VECTOR-SPACE.
;;; =====================================================================





;; ||r.x|| = |r| ||x||, the homogeneity law.  TWO theorems, as nvs-act-laws.scm
;; does: `mac-h' of the IS-X unfold CONSUMES the structure hypothesis, and
;; nvs-scal-carr (carr(scal(m)) == RR) is GUARDED on it -- so the projection
;; keeps the law's own scalar binder and a second, unfold-free proof restates it
;; over RR with the guard still in context.
(r8c-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_))))))))))
(let ((law (r8c-law (lambda (c) (and (pair? c) (eq? (car c) '=)
                                     (pair? (cadr c))
                                     (equal? (car (cadr c)) '(VNRM m))
                                     (pair? (caddr c)) (eq? (car (caddr c)) '*)))
                    "the homogeneity law")))
  (dk-apply! law 'r_ 'x_)
  (ass))
(r8c-check! 'lfe-vnrm-homog-c)

(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL r_ (IMPLIES (IN r_ RR)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_)))))))))))
(dk-peel!)
(r8c-scalar! 'r_)
(fact 'lfe-vnrm-homog-c 'm 'r_ 'x_)
(ass)
(r8c-check! 'lfe-vnrm-homog)

;; ||0|| = 0 (the definiteness law at the zero vector)
(r8c-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (= ((VNRM m) (VZERO m)) 0))))
(let ((law (r8c-law (lambda (c) (and (pair? c) (eq? (car c) 'IFF))) "the definiteness law")))
  (dk-apply! law '(VZERO m))
  (have! '(= (VZERO m) (VZERO m)) (lambda () (rfl)))
  (prop))
(r8c-check! 'lfe-vnrm-vzero)



;;; cancellation in the vector group: x + z = x  =>  z = 0.
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
   (FORALL z_ (IMPLIES (IN z_ (VEC m))
     (IMPLIES (= ((VADD m) x_ z_) x_) (= z_ (VZERO m)))))))))))
(dk-peel!)
(fact 'hbx-vneg-in 'm 'x_)
(fact 'hbx-vneg-left 'm 'x_)
(fact 'hbx-vzero-left 'm 'z_)
(fact 'nvs-vadd-assoc 'm '((VNEG m) x_) 'x_ 'z_)
(have! '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) z_)
       (lambda () (subst '(= ((VADD m) ((VNEG m) x_) x_) (VZERO m))) (ass)))
(have! '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) (VZERO m))
       (lambda ()
         (subst '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_)
                    ((VADD m) ((VNEG m) x_) ((VADD m) x_ z_))))
         (subst '(= ((VADD m) x_ z_) x_))
         (ass)))
(fact 'eq-sym '((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) 'z_)
(fact 'eq-trans 'z_ '((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) '(VZERO m))
(ass)
(r8c-check! 'lfe-vadd-cancel)

;;; =====================================================================
;;; (3)  THE COEFFICIENT IS UNIQUE, up to the factor ||v||.
;;; =====================================================================

(sp (make-wff '(FORALL m (FORALL v
   (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
   (FORALL a_ (IMPLIES (IN a_ RR)
   (FORALL b_ (IMPLIES (IN b_ RR)
     (IMPLIES (= ((ACT m) a_ v) ((ACT m) b_ v))
       (= (* a_ ((VNRM m) v)) (* b_ ((VNRM m) v))))))))))))))
(dk-peel!)
(fact 'vnrm-real 'm 'v)
(fact 'rr-sub-in-rr 'a_ 'b_)
(fact 'nvs-act-in-vec 'm 'a_ 'v)
(fact 'nvs-act-in-vec 'm 'b_ 'v)
(fact 'nvs-act-in-vec 'm '(- a_ b_) 'v)
(fact 'hbx-act-sum 'm 'b_ '(- a_ b_) 'v)
(have! '(= (+ b_ (- a_ b_)) a_) (lambda () (crs)))
;; b.v + (a-b).v = a.v, and a.v = b.v, so b.v + (a-b).v = b.v: cancel.
(have! '(= ((VADD m) ((ACT m) b_ v) ((ACT m) (- a_ b_) v)) ((ACT m) a_ v))
  (lambda ()
    (subst '(= ((VADD m) ((ACT m) b_ v) ((ACT m) (- a_ b_) v))
               ((ACT m) (+ b_ (- a_ b_)) v)))
    (subst '(= (+ b_ (- a_ b_)) a_))
    (rfl)))
(have! '(= ((VADD m) ((ACT m) b_ v) ((ACT m) (- a_ b_) v)) ((ACT m) b_ v))
  (lambda ()
    (subst '(= ((VADD m) ((ACT m) b_ v) ((ACT m) (- a_ b_) v)) ((ACT m) a_ v)))
    (ass)))
(fact 'lfe-vadd-cancel 'm '((ACT m) b_ v) '((ACT m) (- a_ b_) v))
;; so |a-b| * ||v|| = ||0|| = 0
(fact 'lfe-vnrm-homog 'm '(- a_ b_) 'v)
(fact 'lfe-vnrm-vzero 'm)
(have! '(= (* (abs (- a_ b_)) ((VNRM m) v)) 0)
  (lambda ()
    (subst '(= (* (abs (- a_ b_)) ((VNRM m) v)) ((VNRM m) ((ACT m) (- a_ b_) v))))
    (subst '(= ((ACT m) (- a_ b_) v) (VZERO m)))
    (ass)))
(fact 'rr-abs-closed '(- a_ b_))
(fact 'rr-no-zero-divisors '(abs (- a_ b_)) '((VNRM m) v))
(use-cases (list '(= (abs (- a_ b_)) 0) '(= ((VNRM m) v) 0))
  ;; |a-b| = 0, so a = b
  (lambda ()
    (fact 'rr-abs-zero '(- a_ b_))
    (have! '(= (- a_ b_) 0) (lambda () (prop)))
    (have! '(= (* a_ ((VNRM m) v))
               (+ (* (- a_ b_) ((VNRM m) v)) (* b_ ((VNRM m) v))))
           (lambda () (crs)))
    (subst '(= (* a_ ((VNRM m) v))
               (+ (* (- a_ b_) ((VNRM m) v)) (* b_ ((VNRM m) v)))))
    (subst '(= (- a_ b_) 0))
    (crs))
  ;; ||v|| = 0: both sides are 0
  (lambda ()
    (subst '(= ((VNRM m) v) 0))
    (crs)))
(r8c-check! 'lfe-coef-unique)

;;; =====================================================================
;;; (4)  THE DESCRIPTION DENOTES, and its value.
;;;
;;; LFE-BODY(u) = IOTA t. t in RR and (some q in RR with u = q.v and t = q||v||)
;;; -- "the coefficient of u on the line RR.v, scaled by ||v||".  It is a
;;; definite description ALSO when v = 0: then ||v|| = 0 and every admissible t
;;; is 0, so no case split is needed anywhere below.
;;; =====================================================================

(define (r8c-iota-of u)
  (list 'IOTA 't_
        (list 'AND '(IN t_ RR)
              (list 'FORSOME 'q_
                    (list 'AND '(IN q_ RR)
                          (list 'AND (list '= u '((ACT m) q_ v))
                                '(= t_ (* q_ ((VNRM m) v)))))))))

;; From (= u_ (c_.v)) and (= u_ (q.v)) in context: land (= (* c_ ||v||) (* q ||v||)).
(define (r8c-same-coef! q)
  (fact 'eq-sym 'u_ '((ACT m) c_ v))
  (fact 'eq-trans '((ACT m) c_ v) 'u_ (list '(ACT m) q 'v))
  (fact 'lfe-coef-unique 'm 'v 'c_ q))

(define (r8c-fresh-in-goal! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (x)
                (if (not (memq x fv))
                    (error "rake-line-functional: eigenvariable not in goal" x
                           (expression->string (dk-goal)))))
              vars)))

(define r8c-value-statement
  (list 'FORALL 'm
    (list 'FORALL 'v
      (list 'FORALL 'u_
        (list 'FORALL 'c_
          (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
            (list 'IMPLIES '(IN v (VEC m))
              (list 'IMPLIES '(IN c_ RR)
                (list 'IMPLIES '(= u_ ((ACT m) c_ v))
                  (list '= (r8c-iota-of 'u_) '(* c_ ((VNRM m) v))))))))))))

(sp (make-wff r8c-value-statement))
(dk-peel!)
(r8c-fresh-in-goal! '(u_ c_))
(fact 'vnrm-real 'm 'v)
(have! '(AND (IN c_ RR) (IN ((VNRM m) v) RR)))
(fact 'rr-mul-closed 'c_ '((VNRM m) v))
(fact 'nvs-act-in-vec 'm 'c_ 'v)
(let ((r8c-io (cadr (dk-goal))))
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         ;; -------- existence and uniqueness: the witness is c_ * ||v|| --------
         (begin
           (ew '(* c_ ((VNRM m) v)))
           (dk-conj-close!
            (lambda ()
              (let ((g (dk-goal)))
                (cond
                  ((eq? (car g) 'IN) (ass))
                  ;; the description's own body at the witness
                  ((eq? (car g) 'FORSOME)
                   (ew 'c_)
                   (dk-conj-close!
                    (lambda ()
                      (let ((h (dk-goal)))
                        (if (and (eq? (car h) '=) (equal? (cadr h) (caddr h)))
                            (rfl)
                            (ass))))))
                  ;; uniqueness: any other admissible value is the same
                  ((eq? (car g) 'FORALL)
                   (dk-peel!)
                   (dk-split-all!)
                   (let* ((y  (caddr (dk-goal)))
                          (q1 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the other decomposition"))))
                     (r8c-same-coef! q1)
                     (subst (list '= y (list '* q1 '((VNRM m) v))))
                     (ass)))
                  (#t (error "rake-line-functional: unexpected exuniq conjunct"
                             (expression->string g))))))))
         ;; -------- the main branch: the granted property pins the value --------
         (begin
           (dk-split-all!)
           (let ((q0 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the granted decomposition"))))
             (r8c-same-coef! q0)
             (subst (list '= r8c-io (list '* q0 '((VNRM m) v))))
             (fact 'eq-sym '(* c_ ((VNRM m) v)) (list '* q0 '((VNRM m) v)))
             (ass)))))
   (dk-opened (lambda () (iota-d r8c-io)))))
(r8c-check! 'lfe-coef-value)

;;; =====================================================================
;;; (5)  line-functional-exists -- norm-as-sup-proof.scm:43
;;; =====================================================================

(define r8c-line '(LINE m v))
(define r8c-nrm '((VNRM m) v))
(define r8c-F (list 'VNB-LAMBDA 'u_ r8c-line (r8c-iota-of 'u_)))

;; the decomposition of a point of the line: land its typing and skolemize its
;; coefficient.  Returns the coefficient.
(define (r8c-decompose! u)
  (fact 'lfe-line-in-vec 'm 'v u)
  (dk-fact! 'lfe-line-coef 'm 'v u)
  (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME) (memq u (free-vars f))))
                       "the decomposition of a point of the line")))

;; close a conjunct that is a reflexive equation by `rfl', anything else by `ass'
(define (r8c-refl-or-ass!)
  (let ((h (dk-goal)))
    (if (and (eq? (car h) '=) (equal? (cadr h) (caddr h))) (rfl) (ass))))

(define (r8c-additive? g)
  (let ((c (r8c-core g))) (and (eq? (car c) '=) (pair? (caddr c)) (eq? (car (caddr c)) '+))))

(sp (make-wff '(FORALL m (FORALL v
   (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
     (FORSOME f_ (AND (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m (LINE m v) f_)
                 (AND (<= (DUAL-NORM-ON m (LINE m v) f_) 1)
                      (= (f_ v) ((VNRM m) v)))))))))))
(dk-peel!)
(r8c-fresh-in-goal! '(m v))
(fact 'vnrm-real 'm 'v)
(fact 'vnrm-nonneg 'm 'v)
(fact 'vec-is-set 'm)
(fact 'rr-one-in)
(have! '(<= 0 1) (lambda () (arith)))
(fact 'hbx-act-one 'm 'v)
(fact 'eq-sym '((ACT m) 1 v) 'v)                 ; v = 1.v
(fact 'lfe-line-mem-eq 'm 'v 'v 1)               ; v in LINE(m,v)

;;; ---- (A) the lambda is a linear functional on the line ----
(have! (list 'IS-LINEAR-FUNCTIONAL-ON 'm r8c-line r8c-F)
  (lambda ()
    (mac 'IS-LINEAR-FUNCTIONAL-ON)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
           ;; the FUN typing: sethood of the line, then the pointwise value
           ((eq? (car g) 'IN)
            (for-each
             (lambda (leaf)
               (dk-focus! leaf)
               (if (equal? (dk-goal) (list 'IN r8c-line 'SET))
                   (begin (mac 'LINE) (sep-set) (ass))
                   (let* ((u (dk-di-var!))
                          (q (r8c-decompose! u)))
                     (fact 'lfe-coef-value 'm 'v u q)
                     (subst (list '= (r8c-iota-of u) (list '* q r8c-nrm)))
                     (have! (list 'AND (list 'IN q 'RR) (list 'IN r8c-nrm 'RR)))
                     (fact 'rr-mul-closed q r8c-nrm)
                     (ass))))
             (dk-opened (lambda () (lam-t)))))
           ;; additivity
           ((r8c-additive? g)
            (let* ((landed (dk-peel!))
                   (xs (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                          (equal? (caddr f) r8c-line)))
                                         landed)))
                   (x1 (car xs)) (x2 (cadr xs))
                   (a (r8c-decompose! x1))
                   (b (r8c-decompose! x2))
                   (sum (list '(VADD m) x1 x2))
                   (ab (list '+ a b)))
              (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
              (fact 'rr-add-closed a b)
              (have! (list '= sum (list '(ACT m) ab 'v))
                (lambda ()
                  (subst (list '= x1 (list '(ACT m) a 'v)))
                  (subst (list '= x2 (list '(ACT m) b 'v)))
                  (fact 'hbx-act-sum 'm a b 'v)
                  (ass)))
              (fact 'lfe-line-mem-eq 'm 'v sum ab)
              (lam-b)
              (fact 'lfe-coef-value 'm 'v x1 a)
              (fact 'lfe-coef-value 'm 'v x2 b)
              (fact 'lfe-coef-value 'm 'v sum ab)
              (subst (list '= (r8c-iota-of sum) (list '* ab r8c-nrm)))
              (subst (list '= (r8c-iota-of x1) (list '* a r8c-nrm)))
              (subst (list '= (r8c-iota-of x2) (list '* b r8c-nrm)))
              (crs)))
           ;; homogeneity
           (#t
            (let* ((landed (dk-peel!))
                   (r (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (equal? (caddr f) 'RR)
                                                      (memq (cadr f) (map cadr (filter pair? landed)))))
                                     "the scalar")))
                   (x (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (equal? (caddr f) r8c-line)
                                                      (memq f landed)))
                                     "the point of the line")))
                   (q (r8c-decompose! x))
                   (rx (list '(ACT m) r x))
                   (rq (list '* r q)))
              (have! (list 'AND (list 'IN r 'RR) (list 'IN q 'RR)))
              (fact 'rr-mul-closed r q)
              (have! (list '= rx (list '(ACT m) rq 'v))
                (lambda ()
                  (subst (list '= x (list '(ACT m) q 'v)))
                  (fact 'nvs-act-scale-assoc 'm r q 'v)
                  (ass)))
              (fact 'lfe-line-mem-eq 'm 'v rx rq)
              (lam-b)
              (fact 'lfe-coef-value 'm 'v x q)
              (fact 'lfe-coef-value 'm 'v rx rq)
              (subst (list '= (r8c-iota-of rx) (list '* rq r8c-nrm)))
              (subst (list '= (r8c-iota-of x) (list '* q r8c-nrm)))
              (crs)))))))))

;;; ---- (B) 1 is a bound: |f(w)| = ||w|| on the line ----
(have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r8c-line)
         (list '<= (list 'abs (list r8c-F 'w_)) (list '* 1 (list '(VNRM m) 'w_)))))
  (lambda ()
    (dk-peel!)
    (let* ((w (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                              (equal? (caddr f) r8c-line)))
                             "the point of the line")))
           (q (r8c-decompose! w)))
      (lam-b)
      (fact 'lfe-coef-value 'm 'v w q)
      (subst (list '= (r8c-iota-of w) (list '* q r8c-nrm)))
      (subst (list '= w (list '(ACT m) q 'v)))
      (fact 'lfe-vnrm-homog 'm q 'v)
      (subst (list '= (list '(VNRM m) (list '(ACT m) q 'v)) (list '* (list 'abs q) r8c-nrm)))
      (have! (list 'AND (list 'IN q 'RR) (list 'IN r8c-nrm 'RR)))
      (fact 'rr-abs-mult q r8c-nrm)
      (subst (list '= (list 'abs (list '* q r8c-nrm))
                   (list '* (list 'abs q) (list 'abs r8c-nrm))))
      (fact 'rr-abs-of-nonneg r8c-nrm)
      (subst (list '= (list 'abs r8c-nrm) r8c-nrm))
      (fact 'rr-abs-closed q)
      (have! (list 'AND (list 'IN (list 'abs q) 'RR) (list 'IN r8c-nrm 'RR)))
      (fact 'rr-mul-closed (list 'abs q) r8c-nrm)
      (have! (list '= (list '* 1 (list '* (list 'abs q) r8c-nrm))
                   (list '* (list 'abs q) r8c-nrm))
             (lambda () (crs)))
      (subst (list '= (list '* 1 (list '* (list 'abs q) r8c-nrm))
                   (list '* (list 'abs q) r8c-nrm)))
      (fact 'rr-leq-reflexive (list '* (list 'abs q) r8c-nrm))
      (ass))))

;;; ---- (C) the operator norm is at most 1 ----
;;; `dual-norm-on-le-bound-nvs' (theorem-library/rake-dual-norm-spec.scm, batch
;;; 7-A, proven modulo 0) rather than the asserted `dual-norm-on-le-bound' at
;;; hahn-banach-full-proof.scm:49: the guarded form is the one that is true
;;; (7-A's finding -- the unguarded statement leaves ||.|| untyped), it wants
;;; (SUBSET s (VEC m)) where the unguarded one wanted nothing, and citing it is
;;; what takes this proof to `modulo 0'.
(fact 'lfe-line-subset 'm 'v)
(fact 'dual-norm-on-le-bound-nvs 'm r8c-line r8c-F 1)

;;; ---- (D) the value at v is ||v|| ----
(have! (list '= (list r8c-F 'v) r8c-nrm)
  (lambda ()
    (lam-b)
    (fact 'lfe-coef-value 'm 'v 'v 1)
    (subst (list '= (r8c-iota-of 'v) (list '* 1 r8c-nrm)))
    (crs)))

;;; ---- assemble ----
(ew r8c-F)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON)
       (begin
         (mac 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON)
         (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME)
                (begin (ew 1) (dk-conj-close! (lambda () (ass))))
                (ass)))))
       (ass))))
(r8c-check! 'line-functional-exists)

