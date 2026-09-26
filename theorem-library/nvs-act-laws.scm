;;; nvs-act-laws.scm -- THE GROUP AND SCALAR-ACTION LAWS OF A REAL NORMED
;;; VECTOR SPACE.  Since 2026-09-19 (rake batch 8, assignment 8-K1) this file is
;;; their ONE home: section (4) below holds the laws that three to five agents
;;; had each proved separately on 2026-09-19 under their own prefixes.  The NORM
;;; and METRIC laws have their own home, theorem-library/nvs-norm-laws.scm,
;;; which loads immediately after this file.
;;;
;;; Sections (1)-(3) are the original file: THE FIVE SCALAR-ACTION FACTS,
;;; PROVEN.  They were asserted `reference' in
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

;;; =====================================================================
;;; (4) THE NVS GROUP AND ACTION LAWS -- CONSOLIDATED HERE 2026-09-19
;;;     (rake batch 8, assignment 8-K1: "the NVS laws, ONE home").
;;;
;;; Sections (4a)-(4e) below were MOVED here, verbatim, from the files that
;;; proved them on 2026-09-19; each is CUT from its old file and its citations
;;; re-pointed, so install-duplicate-audit stays at zero.  Provenance:
;;;
;;;   (4a) theorem-library/rake-hb-submodules.scm  (batch 7-B), sections (1)-(4)
;;;   (4b) theorem-library/rake-hb-extend-construct.scm (7-C), section (1)
;;;   (4c) theorem-library/directional-derivative.scm (7-F), the spliced block
;;;   (4d) theorem-library/rake-line-functional.scm (7-C)
;;;   (4e) theorem-library/vector-taylor-proof.scm (7-E), the spliced block
;;;
;;; NAMING.  One name per STATEMENT.  Where two statements differ (they are not
;;; alpha-equivalent) both are kept, and the suffix says how:
;;;   -c    the scalar is quantified over CARR(SCAL m)   (nvs-act-distrib-vec
;;;         keeps the bare name for historical reasons; its RR twin is -rr)
;;;   -rr   the scalar is quantified over RR
;;;   -sub  the scalar -1 is written as the SUBTRACTION term (0 - 1), not as the
;;;         literal -1 (nvs-neg-one-act-sub beside nvs-neg-one-act)
;;;   -zero the cancellation concludes z = VZERO m, not z = w
;;;
;;; The moved proofs keep the driver helpers they were written against; the
;;; helper blocks are copied with them, unchanged, so no proof text moved.
;;; =====================================================================

;;; --------------------------------------------------------------------
;;; (4a) from rake-hb-submodules.scm -- helpers, then the ten bricks.
;;; --------------------------------------------------------------------


;;; =====================================================================
;;; (0) FILE-LOCAL DRIVER
;;; =====================================================================

(define r8b-nvs '(IS-NORMED-VECTOR-SPACE m))
(define r8b-pin '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))
(define r8b-neg1 '(- 1))

;; Peel the statement, unfold IS-NORMED-VECTOR-SPACE and split it to atoms, so
;; the structure's own laws sit in the context as citable universals.  Only the
;; three PROJECTIONS use this: mac-h DELETES the hypothesis it unfolds, and
;; every brick after section (2) is guarded on it.
(define (r8b-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8b-nvs)
  (dk-split-all!))

;; Peel only; the guard IS-NORMED-VECTOR-SPACE(m) stays in the context.
(define (r8b-peel! stmt)
  (sp (make-wff stmt))
  (dk-peel!))

(define (r8b-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-hb-submodules: proof did not close" name
             (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;; Eigenvariables are read off the goal, never assumed: `di' renames a binder
;; whose name is taken.
(define (r8b-eigen! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (v)
                (if (not (memq v fv))
                    (error "rake-hb-submodules: eigenvariable not in goal" v
                           (expression->string (dk-goal)))))
              vars)))

;; total list reference: #f off the end, so a predicate may probe any formula
;; in the context without knowing its shape.
(define (r8b-ref lst k)
  (let loop ((l lst) (k k))
    (cond ((not (pair? l)) #f)
          ((= k 0) (car l))
          (#t (loop (cdr l) (- k 1))))))

;; the innermost consequent of a FORALL/IMPLIES tower
(define (r8b-core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (r8b-core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (r8b-core (caddr f)))
        (#t f)))

;; A law of the IS-NORMED-VECTOR-SPACE unfold, instantiated at the goal's
;; eigenvariables and closed by `ass'.  FIND picks the law by its CORE.
(define (r8b-project! name stmt find vars)
  (r8b-open! stmt)
  (r8b-eigen! vars)
  (let ((law (dk-pick (lambda (f) (find (r8b-core f))) name)))
    (apply dk-apply! law vars)
    (ass))
  (r8b-check! name))

;; an in-context equation, used RIGHT TO LEFT
(define (r8b-back eq) (list '= (caddr eq) (cadr eq)))

;; (IN r (CARR (SCAL m))) from (IN r RR), by the carrier read-off.
(define (r8b-scalar! r)
  (have! (list 'IN r '(CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

;;; =====================================================================
;;; (1) THE NEG SLOT OF THE SCALARS (nvs-act-laws does CARR/ADD/MUL/ZERO/ONE)
;;; =====================================================================

;;; neg(scal(m)) == vnb-lambda(x_, rr, -x_).  Proved exactly as nvs-act-laws'
;;; `nal-scalar-slot!': `subst' the pinning law in ARGUMENT position (SCAL sits
;;; under NEG as an argument, where replace-term reaches), then the generic
;;; read-off of the RR-NORMED-FIELD projection.
(r8b-open! `(FORALL m (IMPLIES ,r8b-nvs
   (== (NEG (SCAL m)) (VNB-LAMBDA x_ RR (- x_))))))
(subst r8b-pin)
(mac 'rr-scalar-ring-neg)
(qrfl)
(r8b-check! 'nvs-scal-neg)

;;; =====================================================================
;;; (2) PROJECTIONS OF THE IS-NORMED-VECTOR-SPACE UNFOLD
;;; =====================================================================

;;; vzero(m) + u = u -- the LEFT half of the is-identity conjunct (nvs-act-laws
;;; surfaced the right half as nvs-vzero-right).
(r8b-open! `(FORALL m (IMPLIES ,r8b-nvs
   (FORALL u_ (IMPLIES (IN u_ (VEC m))
     (= ((VADD m) (VZERO m) u_) u_))))))
(r8b-eigen! '(u_))
(let* ((r8b-law (dk-landed-1
                 (lambda () (mac-h 'is-identity '(IS-IDENTITY (VADD m) (VZERO m) (VEC m))))))
       (r8b-both (dk-apply! r8b-law 'u_)))
  (dk-split! r8b-both)
  (ass))
(r8b-check! 'nvs-vzero-left)

;;; u + w = w + u -- the is-commutative conjunct.
(r8b-open! `(FORALL m (IMPLIES ,r8b-nvs
   (FORALL u_ (IMPLIES (IN u_ (VEC m))
   (FORALL w_ (IMPLIES (IN w_ (VEC m))
     (= ((VADD m) u_ w_) ((VADD m) w_ u_)))))))))
(r8b-eigen! '(u_ w_))
(let ((r8b-law (dk-landed-1
                (lambda () (mac-h 'is-commutative '(IS-COMMUTATIVE (VADD m) (VEC m)))))))
  (dk-apply! r8b-law 'u_ 'w_)
  (ass))
(r8b-check! 'nvs-vadd-comm)

;;; r.(x + y) = r.x + r.y -- the action's distributivity over VADD.
(r8b-project! 'nvs-act-distrib-vec
  `(FORALL m (IMPLIES ,r8b-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((ACT m) r_ ((VADD m) x_ y_))
          ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (equal? (r8b-ref (r8b-ref c 1) 0) '(ACT m))
                   (equal? (r8b-ref (r8b-ref (r8b-ref c 1) 2) 0) '(VADD m))))
  '(r_ x_ y_))

;;; =====================================================================
;;; (3) THE TWO SCALAR-EXTREME ACTION LAWS, THROUGH THE MODULE VIEW
;;; =====================================================================

;;; 0.x = vzero(m).
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((ACT m) 0 x_) (VZERO m)))))))
(r8b-eigen! '(x_))
(fact 'NORMED-VECTOR-SPACE-AS-MODULE-is-MODULE 'm)
(have! '(IN x_ (VEC (NORMED-VECTOR-SPACE-AS-MODULE m)))
       (lambda () (mac 'nvs-module-view-vec) (ass)))
(let* ((r8b-l0 (dk-fact! 'module-zero-act '(NORMED-VECTOR-SPACE-AS-MODULE m) 'x_))
       (r8b-l1 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-act   r8b-l0))))
       (r8b-l2 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-scal  r8b-l1))))
       (r8b-l3 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-vzero r8b-l2)))))
  (if (not (equal? r8b-l3 '(= ((ACT m) (ZERO (SCAL m)) x_) (VZERO m))))
      (error "rake-hb-submodules: module-zero-act did not carry back"
             (expression->string r8b-l3)))
  (have! '(== (ZERO (SCAL m)) 0) (lambda () (mac 'nvs-scal-zero) (qrfl)))
  (subst '(== 0 (ZERO (SCAL m))))
  (ass))
(r8b-check! 'nvs-zero-act)

;;; (-1).x = -x.  The scalar (neg(scal m))(one(scal m)) is reduced to the
;;; literal -1 by nvs-scal-one, nvs-scal-neg and the unary lambda-slot
;;; application law.
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((ACT m) (- 1) x_) ((VNEG m) x_)))))))
(r8b-eigen! '(x_))
(fact 'NORMED-VECTOR-SPACE-AS-MODULE-is-MODULE 'm)
(have! '(IN x_ (VEC (NORMED-VECTOR-SPACE-AS-MODULE m)))
       (lambda () (mac 'nvs-module-view-vec) (ass)))
(fact 'rr-one-in)
(let* ((r8b-l0 (dk-fact! 'module-act-neg-one '(NORMED-VECTOR-SPACE-AS-MODULE m) 'x_))
       (r8b-l1 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-act  r8b-l0))))
       (r8b-l2 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-scal r8b-l1))))
       (r8b-l3 (dk-landed-1 (lambda () (mac-h 'nvs-module-view-vneg r8b-l2)))))
  (if (not (equal? r8b-l3
                   '(= ((ACT m) ((NEG (SCAL m)) (ONE (SCAL m))) x_) ((VNEG m) x_))))
      (error "rake-hb-submodules: module-act-neg-one did not carry back"
             (expression->string r8b-l3)))
  (have! '(== ((NEG (SCAL m)) (ONE (SCAL m))) (- 1))
         (lambda ()
           (mac 'nvs-scal-one) (mac 'nvs-scal-neg) (mac 'lam-slot-neg-apply) (qrfl)))
  (subst '(== (- 1) ((NEG (SCAL m)) (ONE (SCAL m)))))
  (ass))
(r8b-check! 'nvs-neg-one-act)

;;; =====================================================================
;;; (4) THE ARITHMETIC BRICKS THE SUBMODULE PROOFS REARRANGE WITH
;;; =====================================================================

;;; r.x + s.x = (r+s).x.
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL r_ (IMPLIES (IN r_ RR)
   (FORALL s_ (IMPLIES (IN s_ RR)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((VADD m) ((ACT m) r_ x_) ((ACT m) s_ x_))
        ((ACT m) (+ r_ s_) x_)))))))))))
(r8b-eigen! '(r_ s_ x_))
(r8b-scalar! 'r_) (r8b-scalar! 's_)
(have! '(== ((ADD (SCAL m)) r_ s_) (+ r_ s_))
       (lambda () (mac 'nvs-scal-add) (mac 'lam-slot-add-apply) (qrfl)))
(subst '(== (+ r_ s_) ((ADD (SCAL m)) r_ s_)))
(let ((r8b-law (dk-fact! 'nvs-act-distrib-scalar 'm 'r_ 's_ 'x_)))
  (fact 'eq-sym (cadr r8b-law) (caddr r8b-law))
  (ass))
(r8b-check! 'nvs-act-add-scalars)

;;; -(r.x) = ((-1)*r).x.
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL r_ (IMPLIES (IN r_ RR)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (= ((VNEG m) ((ACT m) r_ x_)) ((ACT m) (* (- 1) r_) x_)))))))))
(r8b-eigen! '(r_ x_))
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(fact 'nvs-act-in-vec 'm 'r_ 'x_)
(subst (r8b-back (dk-fact! 'nvs-neg-one-act 'm '((ACT m) r_ x_))))
(dk-fact! 'nvs-act-scale-assoc 'm r8b-neg1 'r_ 'x_)
(ass)
(r8b-check! 'nvs-act-vneg)

;;; -(x + y) = (-x) + (-y).
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
   (FORALL y_ (IMPLIES (IN y_ (VEC m))
     (= ((VNEG m) ((VADD m) x_ y_))
        ((VADD m) ((VNEG m) x_) ((VNEG m) y_))))))))))
(r8b-eigen! '(x_ y_))
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(r8b-scalar! r8b-neg1)
(fact 'nvs-vadd-in-vec 'm 'x_ 'y_)
(subst (r8b-back (dk-fact! 'nvs-neg-one-act 'm '((VADD m) x_ y_))))
(subst (r8b-back (dk-fact! 'nvs-neg-one-act 'm 'x_)))
(subst (r8b-back (dk-fact! 'nvs-neg-one-act 'm 'y_)))
(dk-fact! 'nvs-act-distrib-vec 'm r8b-neg1 'x_ 'y_)
(ass)
(r8b-check! 'nvs-vneg-vadd)

;;; (a + c) + (b + d) = (a + b) + (c + d) -- the one rearrangement
;;; span-add-one-submodule's addition conjunct needs.  Associativity and
;;; commutativity, five substitutions, both sides driven to a + (b + (c + d)).
(r8b-peel! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL a_ (IMPLIES (IN a_ (VEC m))
   (FORALL b_ (IMPLIES (IN b_ (VEC m))
   (FORALL c_ (IMPLIES (IN c_ (VEC m))
   (FORALL d_ (IMPLIES (IN d_ (VEC m))
     (= ((VADD m) ((VADD m) a_ c_) ((VADD m) b_ d_))
        ((VADD m) ((VADD m) a_ b_) ((VADD m) c_ d_))))))))))))))
(r8b-eigen! '(a_ b_ c_ d_))
(fact 'nvs-vadd-in-vec 'm 'b_ 'd_)
(fact 'nvs-vadd-in-vec 'm 'c_ 'd_)
(fact 'nvs-vadd-in-vec 'm 'c_ 'b_)
(fact 'nvs-vadd-in-vec 'm 'b_ 'c_)
;; (a+c)+(b+d) -> a+(c+(b+d))
(subst (dk-fact! 'nvs-vadd-assoc 'm 'a_ 'c_ '((VADD m) b_ d_)))
;; (a+b)+(c+d) -> a+(b+(c+d))
(subst (dk-fact! 'nvs-vadd-assoc 'm 'a_ 'b_ '((VADD m) c_ d_)))
;; c+(b+d) -> (c+b)+d   (the assoc law used RIGHT TO LEFT)
(subst (r8b-back (dk-fact! 'nvs-vadd-assoc 'm 'c_ 'b_ 'd_)))
;; c+b -> b+c
(subst (dk-fact! 'nvs-vadd-comm 'm 'c_ 'b_))
;; (b+c)+d -> b+(c+d)
(subst (dk-fact! 'nvs-vadd-assoc 'm 'b_ 'c_ 'd_))
(fact 'nvs-vadd-in-vec 'm 'b_ '((VADD m) c_ d_))
(fact 'nvs-vadd-in-vec 'm 'a_ '((VADD m) b_ ((VADD m) c_ d_)))
(rfl)
(r8b-check! 'nvs-vadd-shuffle)

;;; --------------------------------------------------------------------
;;; (4b) from rake-hb-extend-construct.scm -- the vector group.  Four of its
;;; eleven theorems were alpha-equivalent to (4a)'s and are gone: hbx-vzero-left
;;; (= nvs-vzero-left), hbx-vadd-comm (= nvs-vadd-comm), hbx-act-distrib-c
;;; (= nvs-act-distrib-vec), hbx-act-sum (= nvs-act-add-scalars).
;;; --------------------------------------------------------------------

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

;;; =====================================================================

(r8h-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IN (VZERO m) (VEC m)))))
(ass)
(r8h-check! 'nvs-vzero-in-vec)

(r8h-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m)) (IN ((VNEG m) x_) (VEC m)))))))
(fact 'fun-apply-type-c '(VNEG m) '(VEC m) '(VEC m) 'x_)
(ass)
(r8h-check! 'nvs-vneg-in-vec)

;;; (-u) + u = vzero -- the LEFT half of the has-inverses conjunct.
(r8h-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL u_ (IMPLIES (IN u_ (VEC m))
     (= ((VADD m) ((VNEG m) u_) u_) (VZERO m)))))))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'has-inverses
                               '(HAS-INVERSES (VADD m) (VZERO m) (VNEG m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8h-check! 'nvs-vneg-left)

(sp (make-wff
 '(FORALL m
    (IMPLIES (IS-NORMED-VECTOR-SPACE m)
      (FORALL r_
        (IMPLIES (IN r_ RR)
          (FORALL x_
            (IMPLIES (IN x_ (VEC m))
              (FORALL y_
                (IMPLIES (IN y_ (VEC m))
                  (= ((ACT m) r_ ((VADD m) x_ y_))
                     ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))))))
(dk-peel!)
(have! '(IN r_ (CARR (SCAL m))) (lambda () (mac 'nvs-scal-carr) (ass)))
(fact 'nvs-act-distrib-vec 'm 'r_ 'x_ 'y_)
(ass)
(r8h-check! 'nvs-act-distrib-vec-rr)

;;; 1.x = x
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m)) (= ((ACT m) 1 x_) x_)))))))
(dk-peel!)
(have! '(== (ONE (SCAL m)) 1) (lambda () (mac 'nvs-scal-one) (qrfl)))
(subst '(== 1 (ONE (SCAL m))))
(fact 'nvs-act-unital 'm 'x_)
(ass)
(r8h-check! 'nvs-one-act)

;;; x + z = x + w  =>  z = w
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
   (FORALL z_ (IMPLIES (IN z_ (VEC m))
   (FORALL w_ (IMPLIES (IN w_ (VEC m))
     (IMPLIES (= ((VADD m) x_ z_) ((VADD m) x_ w_)) (= z_ w_))))))))))))
(dk-peel!)
(fact 'nvs-vneg-in-vec 'm 'x_)
(fact 'nvs-vneg-left 'm 'x_)
(fact 'nvs-vzero-left 'm 'z_)
(fact 'nvs-vzero-left 'm 'w_)
(fact 'nvs-vadd-assoc 'm '((VNEG m) x_) 'x_ 'z_)
(fact 'nvs-vadd-assoc 'm '((VNEG m) x_) 'x_ 'w_)
(have! '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) z_)
       (lambda () (subst '(= ((VADD m) ((VNEG m) x_) x_) (VZERO m))) (ass)))
(have! '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) w_) w_)
       (lambda () (subst '(= ((VADD m) ((VNEG m) x_) x_) (VZERO m))) (ass)))
(have! '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_)
           ((VADD m) ((VADD m) ((VNEG m) x_) x_) w_))
       (lambda ()
         (subst '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) z_)
                    ((VADD m) ((VNEG m) x_) ((VADD m) x_ z_))))
         (subst '(= ((VADD m) x_ z_) ((VADD m) x_ w_)))
         (subst '(= ((VADD m) ((VADD m) ((VNEG m) x_) x_) w_)
                    ((VADD m) ((VNEG m) x_) ((VADD m) x_ w_))))
         (rfl)))
(fact 'eq-sym '((VADD m) ((VADD m) ((VNEG m) x_) x_) z_) 'z_)
(fact 'eq-trans 'z_ '((VADD m) ((VADD m) ((VNEG m) x_) x_) z_)
                   '((VADD m) ((VADD m) ((VNEG m) x_) x_) w_))
(fact 'eq-trans 'z_ '((VADD m) ((VADD m) ((VNEG m) x_) x_) w_) 'w_)
(ass)
(r8h-check! 'nvs-vadd-cancel)

;;; z + x = w + x  =>  z = w  (commutativity, then the left form)
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
   (FORALL z_ (IMPLIES (IN z_ (VEC m))
   (FORALL w_ (IMPLIES (IN w_ (VEC m))
     (IMPLIES (= ((VADD m) z_ x_) ((VADD m) w_ x_)) (= z_ w_))))))))))))
(dk-peel!)
(fact 'nvs-vadd-comm 'm 'z_ 'x_)
(fact 'nvs-vadd-comm 'm 'w_ 'x_)
(have! '(= ((VADD m) x_ z_) ((VADD m) x_ w_))
       (lambda ()
         (subst '(= ((VADD m) x_ z_) ((VADD m) z_ x_)))
         (subst '(= ((VADD m) z_ x_) ((VADD m) w_ x_)))
         (subst '(= ((VADD m) w_ x_) ((VADD m) x_ w_)))
         (rfl)))
(fact 'nvs-vadd-cancel 'm 'x_ 'z_ 'w_)
(ass)
(r8h-check! 'nvs-vadd-cancel-right)


;;; --------------------------------------------------------------------
;;; (4c) from directional-derivative.scm -- u + (-u) = vzero, the RIGHT half.
;;; --------------------------------------------------------------------
(define r8f-nvs   r8h-nvs)
(define r8f-open! r8h-open!)
(define (r8f-eigen! vars) (r8b-eigen! vars))
(define (r8f-check! name) (r8h-check! name))
(define (r8c-check! name) (r8h-check! name))
(define (r8e-check! name) (r8h-check! name))

;;; u + (-u) = 0  -- the right half of the has-inverses property conjunct
(r8f-open!
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL u_ (IMPLIES (IN u_ (VEC m))
       (= ((VADD m) u_ ((VNEG m) u_)) (VZERO m)))))))
(r8f-eigen! '(u_))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'has-inverses
                               '(HAS-INVERSES (VADD m) (VZERO m) (VNEG m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8f-check! 'nvs-vneg-right)


;;; --------------------------------------------------------------------
;;; (4d) from rake-line-functional.scm -- cancellation to VZERO.
;;; --------------------------------------------------------------------

;;; cancellation in the vector group: x + z = x  =>  z = 0.
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (FORALL x_ (IMPLIES (IN x_ (VEC m))
   (FORALL z_ (IMPLIES (IN z_ (VEC m))
     (IMPLIES (= ((VADD m) x_ z_) x_) (= z_ (VZERO m)))))))))))
(dk-peel!)
(fact 'nvs-vneg-in-vec 'm 'x_)
(fact 'nvs-vneg-left 'm 'x_)
(fact 'nvs-vzero-left 'm 'z_)
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
(r8c-check! 'nvs-vadd-cancel-zero)


;;; --------------------------------------------------------------------
;;; (4e) from vector-taylor-proof.scm -- (0 - 1).u = -u.  NOT the same
;;; statement as nvs-neg-one-act above: the scalar is the subtraction term
;;; (0 - 1), not the literal -1, and no rewrite in the tree identifies them in
;;; a term position, so both are kept.
;;; --------------------------------------------------------------------

(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
          (= ((ACT m) (- 0 1) u_) ((VNEG m) u_))))))))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 1)
(fact 'nvs-vneg-in-vec 'm 'u_)
(fact 'nvs-act-in-vec 'm '(- 0 1) 'u_)
(fact 'nvs-vzero-left 'm '((ACT m) (- 0 1) u_))
(subst '(= ((ACT m) (- 0 1) u_) ((VADD m) (VZERO m) ((ACT m) (- 0 1) u_))))
(fact 'nvs-vneg-left 'm 'u_)
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
(r8e-check! 'nvs-neg-one-act-sub)
