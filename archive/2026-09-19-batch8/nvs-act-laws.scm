;;; nvs-act-laws.scm -- THE FIVE SCALAR-ACTION FACTS OF A REAL NORMED VECTOR
;;; SPACE, PROVEN.  They were asserted `reference' in
;;; theorem-library/directional-derivative.scm:151-220:
;;;
;;;   nvs-act-in-vec       r.x in vec(m)                       (r in RR, x in vec(m))
;;;   nvs-act-scale-assoc  r.(s.x) = (r*s).x
;;;   nvs-act-collect      (y + r.x) + s.x = y + (r+s).x
;;;   nvs-act-zero         y + 0.x = y
;;;   nvs-act-one          y + 1.x = y + x
;;;
;;; Each is a module law of IS-NORMED-VECTOR-SPACE read with the scalars spelled
;;; as reals.  The structure's laws quantify `r_ in carr(scal(m))' and apply
;;; `add(scal(m))', `mul(scal(m))', `one(scal(m))'; the pinning law
;;;     scal(m) = normed-field-as-commutative-ring(rr-normed-field)
;;; is a conjunct of the same unfold, and theorem-library/normed-field-ring-view.scm
;;; reads the six slots of that projection off (`rr-scalar-ring-carr' : carr == RR,
;;; `-add' / `-mul' : the tupled VNB-LAMBDAs, `-zero' : 0, `-one' : 1).  So every
;;; scalar-side step is one rewrite.
;;;
;;; THE ONE MECHANIC THAT SHAPES THE FILE.  `subst' (pi-eq-subst!, replace-term)
;;; never walks into OPERATOR position -- `(cons (car e) (map walk (cdr e)))' --
;;; so the in-context pinning equation cannot rewrite `(SCAL m)' inside
;;; `((MUL (SCAL m)) r_ s_)'.  A MACETE can, but the pinning is an assumption, not
;;; a named theorem.  Hence section (1): five NAMED, GUARDED read-offs
;;;     forall m. is-nvs(m) => carr(scal(m)) == RR          (nvs-scal-carr)
;;;                            mul(scal(m))  == (VNB-LAMBDA ...)   (nvs-scal-mul) ...
;;; each proved by `subst' of the pinning in ARGUMENT position (the goal is
;;; `(== (MUL (SCAL m)) ...)', where SCAL sits under MUL as an argument) and one
;;; `mac' of the normed-field-ring-view read-off.  With IS-NORMED-VECTOR-SPACE m
;;; in context they fire by `mac' anywhere, operator position included.
;;;
;;; Section (2) projects the four action laws and the two abelian-group facts
;;; the five theorems need out of the unfold, as guarded theorems -- so the main
;;; proofs never unfold IS-NORMED-VECTOR-SPACE themselves and keep the guard the
;;; section-(1) macetes need.  `nvs-act-type' is op-typing.scm's driver with the
;;; scalar carrier left as `carr(scal(m))'; the CLAUDE.md note that the pair
;;; "does not type without the normed-field view" was about the RR-binder form,
;;; and the carrier-binder form types directly.
;;;
;;; Section (3) is the five theorems, each a handful of lines.  `nvs-act-zero'
;;; goes through the module view: `module-zero-act' at
;;; NORMED-VECTOR-SPACE-AS-MODULE(m), carried back by the nvs-module-view
;;; read-offs.
;;;
;;; LOAD WINDOW.  After theorem-library/nvs-module-view (nvs-module-view-vec/
;;; act/scal/vzero -- the latest citation; everything else cited is far
;;; earlier: normed-field-ring-view, fun-apply-type-proof, pair-tuple-sethood,
;;; equality-basics, op-typing, lambda-slot-apply, module-zero-act) and BEFORE
;;; theorem-library/directional-derivative, which is the earliest citer of all
;;; five (it cites nvs-act-in-vec from its own proofs).
;;;
;;; Every citation bills `modulo 0', so every theorem here does.
;;; Helper prefix: `nal-'.

(define nal-nvs '(IS-NORMED-VECTOR-SPACE m))
(define nal-pin '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
(define nal-lam-add '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)))
(define nal-lam-mul '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (* x_ y_)))

;; Peel everything (dk-peel!: di until the head is neither FORALL nor IMPLIES;
;; an unguarded antecedent such as IS-NVS(m) takes a second di), unfold, split the
;; unfold to atoms.  Returns the atoms.
(define (nal-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space nal-nvs)
  (dk-split-all!))

(define (nal-check! name)
  (if (not (proof-done? *ps*))
      (error "nvs-act-laws: proof did not close" name (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;; the innermost consequent of a FORALL/IMPLIES tower
(define (nal-core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (nal-core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (nal-core (caddr f)))
        (#t f)))

;; The eigenvariables are read off the goal, never assumed: `di' renames a
;; binder whose name is taken.  Error if a name we are about to instantiate at
;; is not free in the goal.
(define (nal-assert-eigen! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (v)
                (if (not (memq v fv))
                    (error "nvs-act-laws: eigenvariable not in goal" v
                           (expression->string (dk-goal)))))
              vars)))

;;; =====================================================================
;;; (1) THE SCALAR SLOTS OF A NORMED VECTOR SPACE, AS GUARDED MACETES
;;; =====================================================================

(define (nal-scalar-slot! name acc val read-off)
  (nal-open! `(FORALL m (IMPLIES ,nal-nvs (== (,acc (SCAL m)) ,val))))
  (subst nal-pin)                 ; (SCAL m) is an ARGUMENT of acc here
  (mac read-off)
  (qrfl)
  (nal-check! name))

(nal-scalar-slot! 'nvs-scal-carr 'CARR 'RR         'rr-scalar-ring-carr)
(nal-scalar-slot! 'nvs-scal-add  'ADD  nal-lam-add 'rr-scalar-ring-add)
(nal-scalar-slot! 'nvs-scal-mul  'MUL  nal-lam-mul 'rr-scalar-ring-mul)
(nal-scalar-slot! 'nvs-scal-zero 'ZERO 0           'rr-scalar-ring-zero)
(nal-scalar-slot! 'nvs-scal-one  'ONE  1           'rr-scalar-ring-one)

;;; =====================================================================
;;; (2) PROJECTIONS OF THE UNFOLD, GUARDED ON IS-NORMED-VECTOR-SPACE
;;; =====================================================================

;; A law of the unfold, instantiated at the goal's eigenvariables and closed by
;; `ass'.  FIND picks the law by its CORE (the consequent), never by a symbol.
(define (nal-project! name stmt find vars)
  (nal-open! stmt)
  (nal-assert-eigen! vars)
  (let ((law (dk-pick (lambda (f) (find (nal-core f))) name)))
    (apply dk-apply! law vars)
    (ass))
  (nal-check! name))

;; act(add(scal m)(r,s), x) = act(r,x) + act(s,x)
(nal-project! 'nvs-act-distrib-scalar
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) ((ADD (SCAL m)) r_ s_) x_)
          ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_)))))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c)) (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(ADD (SCAL m)))))
  '(r_ s_ x_))

;; act(mul(scal m)(r,s), x) = act(r, act(s,x))
(nal-project! 'nvs-act-mul-compat
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) ((MUL (SCAL m)) r_ s_) x_)
          ((ACT m) r_ ((ACT m) s_ x_)))))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c)) (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(MUL (SCAL m)))))
  '(r_ s_ x_))

;; act(one(scal m), x) = x
(nal-project! 'nvs-act-unital
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) (ONE (SCAL m)) x_) x_)))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c))
                   (equal? (cadr (cadr c)) '(ONE (SCAL m)))))
  '(x_))

;; (u + v) + w = u + (v + w)  -- the is-associative property conjunct
(nal-open!
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL u_ (IMPLIES (IN u_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
     (FORALL w_ (IMPLIES (IN w_ (VEC m))
       (= ((VADD m) ((VADD m) u_ v_) w_)
          ((VADD m) u_ ((VADD m) v_ w_))))))))))))
(nal-assert-eigen! '(u_ v_ w_))
(let ((law (dk-landed-1
            (lambda () (mac-h 'is-associative '(IS-ASSOCIATIVE (VADD m) (VEC m)))))))
  (dk-apply! law 'u_ 'v_ 'w_)
  (ass))
(nal-check! 'nvs-vadd-assoc)

;; u + vzero = u  -- the right half of the is-identity property conjunct
(nal-open!
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL u_ (IMPLIES (IN u_ (VEC m))
       (= ((VADD m) u_ (VZERO m)) u_))))))
(nal-assert-eigen! '(u_))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'is-identity '(IS-IDENTITY (VADD m) (VZERO m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(nal-check! 'nvs-vzero-right)

;; act(r, x) in vec(m) for r in carr(scal m): op-typing.scm's bridge, verbatim
;; -- apply-tupling-2 (a `==', which subst takes), pair-in-cartesian,
;; fun-apply-type-c -- against the shape conjunct
;;   act(m) in fun(cartesian(carr(scal m), vec m), vec m).
(nal-open!
  `(FORALL m (IMPLIES ,nal-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (IN ((ACT m) r_ x_) (VEC m)))))))))
(nal-assert-eigen! '(r_ x_))
(fact 'apply-tupling-2 '(ACT m) 'r_ 'x_)
(subst '(== ((ACT m) r_ x_) ((ACT m) (LIST r_ x_))))
(fact 'pair-in-cartesian '(CARR (SCAL m)) '(VEC m) 'r_ 'x_)
(fact 'fun-apply-type-c '(ACT m) '(CARTESIAN (CARR (SCAL m)) (VEC m)) '(VEC m)
      '(LIST r_ x_))
(ass)
(nal-check! 'nvs-act-type)

;;; =====================================================================
;;; (3) THE FIVE.  IS-NORMED-VECTOR-SPACE m stays in context throughout, so
;;;     the section-(1) macetes fire and the section-(2) facts detach.
;;; =====================================================================

;; (IN r (CARR (SCAL m))) from (IN r RR), by the carrier read-off.
(define (nal-scalar! r)
  (have! `(IN ,r (CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

;; ---- nvs-act-in-vec ----------------------------------------------------
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (IN ((ACT m) r_ x_) (VEC m))))))))))
(dk-peel!)
(nal-assert-eigen! '(r_ x_))
(nal-scalar! 'r_)
(fact 'nvs-act-type 'm 'r_ 'x_)
(ass)
(nal-check! 'nvs-act-in-vec)

;; ---- nvs-act-scale-assoc:  r.(s.x) = (r*s).x ---------------------------
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) r_ ((ACT m) s_ x_)) ((ACT m) (* r_ s_) x_))))))))))))
(dk-peel!)
(nal-assert-eigen! '(r_ s_ x_))
(nal-scalar! 'r_) (nal-scalar! 's_)
;; mul(scal m)(r,s) == r*s: the MUL read-off (operator position: a macete), then
;; the tupled-lambda application law, guarded on r_, s_ in RR (in context).
(have! '(== ((MUL (SCAL m)) r_ s_) (* r_ s_))
       (lambda () (mac 'nvs-scal-mul) (mac 'lam-slot-mul-apply) (qrfl)))
(subst '(== (* r_ s_) ((MUL (SCAL m)) r_ s_)))    ; goal's r*s -> mul(scal m)(r,s)
(let ((law (dk-fact! 'nvs-act-mul-compat 'm 'r_ 's_ 'x_)))
  (fact 'eq-sym (cadr law) (caddr law))
  (ass))
(nal-check! 'nvs-act-scale-assoc)

;; ---- nvs-act-collect:  (y + r.x) + s.x = y + (r+s).x --------------------
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) ((VADD m) y_ ((ACT m) r_ x_)) ((ACT m) s_ x_))
          ((VADD m) y_ ((ACT m) (+ r_ s_) x_)))))))))))))))
(dk-peel!)
(nal-assert-eigen! '(r_ s_ x_ y_))
(nal-scalar! 'r_) (nal-scalar! 's_)
(fact 'nvs-act-in-vec 'm 'r_ 'x_)
(fact 'nvs-act-in-vec 'm 's_ 'x_)
;; reassociate the left side: (y + r.x) + s.x  ->  y + (r.x + s.x)
(subst (dk-fact! 'nvs-vadd-assoc 'm 'y_ '((ACT m) r_ x_) '((ACT m) s_ x_)))
;; r + s -> add(scal m)(r, s), then distribute the action over it
(have! '(== ((ADD (SCAL m)) r_ s_) (+ r_ s_))
       (lambda () (mac 'nvs-scal-add) (mac 'lam-slot-add-apply) (qrfl)))
(subst '(== (+ r_ s_) ((ADD (SCAL m)) r_ s_)))
(subst (dk-fact! 'nvs-act-distrib-scalar 'm 'r_ 's_ 'x_))
;; both sides are now y + (r.x + s.x); rfl wants the term typed
(fact 'nvs-vadd-in-vec 'm '((ACT m) r_ x_) '((ACT m) s_ x_))
(fact 'nvs-vadd-in-vec 'm 'y_ '((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_)))
(rfl)
(nal-check! 'nvs-act-collect)

;; ---- nvs-act-zero:  y + 0.x = y ------------------------------------------
;; 0.x = vzero is module-zero-act at the module view; the four nvs-module-view
;; read-offs carry it back to m, and the ZERO read-off turns zero(scal m) into 0.
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) y_ ((ACT m) 0 x_)) y_)))))))))
(dk-peel!)
(nal-assert-eigen! '(x_ y_))
(fact 'NORMED-VECTOR-SPACE-AS-MODULE-is-MODULE 'm)
(have! '(IN x_ (VEC (NORMED-VECTOR-SPACE-AS-MODULE m)))
       (lambda () (mac 'nvs-module-view-vec) (ass)))
(let* ((l0 (dk-fact! 'module-zero-act '(NORMED-VECTOR-SPACE-AS-MODULE m) 'x_))
       (l1 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-act   l0))))
       (l2 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-scal  l1))))
       (l3 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-vzero l2)))))
  ;; l3:  act(m)(zero(scal m), x_) = vzero(m)
  (if (not (equal? l3 '(= ((ACT m) (ZERO (SCAL m)) x_) (VZERO m))))
      (error "nvs-act-laws: module-zero-act did not carry back as expected"
             (expression->string l3)))
  (have! '(== (ZERO (SCAL m)) 0) (lambda () (mac 'nvs-scal-zero) (qrfl)))
  (subst '(== 0 (ZERO (SCAL m))))         ; goal's 0 -> zero(scal m)
  (subst l3)                              ; act(zero, x) -> vzero
  (fact 'nvs-vzero-right 'm 'y_)
  (ass))
(nal-check! 'nvs-act-zero)

;; ---- nvs-act-one:  y + 1.x = y + x ---------------------------------------
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) y_ ((ACT m) 1 x_)) ((VADD m) y_ x_))))))))))
(dk-peel!)
(nal-assert-eigen! '(x_ y_))
(have! '(== (ONE (SCAL m)) 1) (lambda () (mac 'nvs-scal-one) (qrfl)))
(subst '(== 1 (ONE (SCAL m))))            ; goal's 1 -> one(scal m)
(subst (dk-fact! 'nvs-act-unital 'm 'x_)) ; act(one, x) -> x
(fact 'nvs-vadd-in-vec 'm 'y_ 'x_)        ; rfl wants y + x typed
(rfl)
(nal-check! 'nvs-act-one)
