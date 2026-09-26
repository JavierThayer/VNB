;;; rake-hb-submodules.scm -- the two SUBMODULE leaves of the Hahn-Banach
;;; cluster, PROVEN, and the normed-vector-space action bricks they need.
;;;
;;;   line-is-submodule       theorem-library/norm-as-sup-proof.scm:27-34
;;;   span-add-one-submodule  theorem-library/hahn-banach-full-proof.scm:79-86
;;;
;;; Both statements are their support's statement UNCHANGED.
;;;
;;; THE TWO ARE ONE ARGUMENT.  LINE(m,v) and SPAN-ADD-ONE(m,t,v) are both
;;; separations of VEC(m) by a decomposition condition -- "y = r.v" and
;;; "y = x + r.v with x in t" -- so IS-SUBMODULE's five conjuncts are proved by
;;; one skeleton (`r8b-submodule-drive!') parameterised on the membership
;;; UNFOLD: `r8b-mem-open!' opens a membership hypothesis into its witnesses
;;; and its decomposition equation, `r8b-mem-in!' closes a membership goal from
;;; witnesses.  Only the unfold theorem, the functoid name and the witness
;;; terms differ between the two sets; the peeling, the dispatch, the SEP
;;; plumbing and the typing bookkeeping are shared.
;;;
;;; THE BRICKS (all new, all `modulo 0'; HB-TRIAGE.md asked for the first two):
;;;   nvs-zero-act         (act m)(0, x)  = vzero(m)
;;;   nvs-neg-one-act      (act m)(-1, x) = (vneg m)(x)      [the `-1' companion]
;;;   nvs-scal-neg         neg(scal m) == vnb-lambda(x_, rr, -x_)
;;;   nvs-vzero-left       vzero(m) + u = u
;;;   nvs-vadd-comm        u + w = w + u
;;;   nvs-act-distrib-vec  r.(x + y) = r.x + r.y
;;;   nvs-act-add-scalars  r.x + s.x = (r+s).x
;;;   nvs-act-vneg         -(r.x) = ((-1)*r).x
;;;   nvs-vneg-vadd        -(x + y) = (-x) + (-y)
;;;   nvs-vadd-shuffle     (a + c) + (b + d) = (a + b) + (c + d)
;;;   line-unfold          LINE(m,v) as a citable equation (mac-h needs a
;;;                        THEOREM; a def-functoid installs only a macete)
;;;
;;; nvs-zero-act and nvs-neg-one-act travel through the module view exactly as
;;; nvs-act-zero does (theorem-library/nvs-act-laws.scm:275): `module-zero-act'
;;; / `module-act-neg-one' at NORMED-VECTOR-SPACE-AS-MODULE(m), carried back by
;;; the nvs-module-view read-offs, with the scalar slot read off by
;;; nvs-scal-zero / nvs-scal-one + nvs-scal-neg.
;;;
;;; LOAD WINDOW [507, 508).
;;;   lo = 507: the latest citation is nvs-act-laws (506: nvs-act-scale-assoc,
;;;             nvs-act-distrib-scalar, nvs-vadd-assoc, nvs-vzero-right,
;;;             nvs-act-in-vec, nvs-scal-carr/add/zero/one).  Next latest:
;;;             nvs-module-view (505), span-bricks-proof (406,
;;;             module-act-neg-one), module-zero-act (350), rake-algebra (234,
;;;             span-add-one-unfold), lambda-slot-apply (211), op-typing (207,
;;;             nvs-vadd-in-vec), subset-lemmas (191), normed-field-ring-view
;;;             (157, rr-scalar-ring-neg).
;;;   hi = 508: theorem-library/hahn-banach-full-proof cites
;;;             span-add-one-submodule at :175.  (norm-as-sup-proof, 509, is
;;;             the citer of line-is-submodule, at :150.)
;;;   Recommended slot: immediately after "theorem-library/nvs-act-laws".
;;;   No late tactic is used (no contra / prep / ineq-supply).
;;;
;;; Helper prefix `r8b-'.  Every helper is file-local.

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

;;; MOVED 2026-09-19 (rake batch 8, assignment 8-K1) to
;;; theorem-library/nvs-act-laws.scm, which is now the ONE home of the normed-
;;; vector-space group and action laws (and nvs-norm-laws.scm of the norm laws):
;;;
;;;   nvs-scal-neg, nvs-vzero-left, nvs-vadd-comm, nvs-act-distrib-vec,
;;;   nvs-zero-act, nvs-neg-one-act, nvs-act-add-scalars, nvs-act-vneg,
;;;   nvs-vneg-vadd, nvs-vadd-shuffle -- sections (1)-(4) of this file.
;;; The proofs went over verbatim; nothing here changed but the citations.
;;; The originals are archive/2026-09-19-batch8/.

;;; =====================================================================
;;; (5) LINE AS A CITABLE EQUATION
;;; `def-functoid' installs a rewrite macete and no theorem, so `mac' unfolds
;;; LINE in a GOAL and `mac-h' cannot unfold it in an ASSUMPTION.  The equation
;;; IS provable, and the resulting THEOREM is what mac-h rebuilds its rule from
;;; (rake-algebra.scm does the same for SPAN-ADD-ONE).  `==', not `=': a bare
;;; SEP term is not syntactically defined.
;;; =====================================================================
(sp (make-wff '(FORALL m (FORALL v
   (== (LINE m v)
       (SEP y_ (VEC m)
         (FORSOME r_ (AND (IN r_ RR) (= y_ ((ACT m) r_ v))))))))))
(di) (mac 'LINE) (qrfl)
(qed 'line-unfold)
(gloss! 'line-unfold
  "LINE(m,v) is the separation { y in VEC(m) : y = r.v for some real r }, as a
   citable equation.  Cite it with mac-h to open a membership in a hypothesis.")
(topic! 'line-unfold 'plumbing)

;;; =====================================================================
;;; (6) THE SHARED SUBMODULE SKELETON
;;; =====================================================================

;; Open (IN w S) in the CONTEXT: rewrite S to its SEP by the UNFOLD theorem,
;; sep-me it, and skolemize the decomposition existential to exhaustion.
;; Returns the flat list of atoms it landed: the VEC(m) typing of w, one typing
;; per witness, and the decomposition equation.
(define (r8b-mem-open! unfold hyp)
  (let ((r8b-sep (dk-landed-1 (lambda () (mac-h unfold hyp)))))
    (let loop ((todo (dk-landed (lambda () (sep-me r8b-sep)))) (acc '()))
      (cond ((null? todo) (reverse acc))
            ((eq? (caar todo) 'AND)
             (loop (append (dk-split! (car todo)) (cdr todo)) acc))
            ((eq? (caar todo) 'FORSOME)
             (loop (append (dk-landed (lambda () (ai (car todo)))) (cdr todo)) acc))
            (#t (loop (cdr todo) (cons (car todo) acc)))))))

;; pick an atom out of what r8b-mem-open! returned, by SHAPE, never by position
(define (r8b-atom atoms pred what)
  (let ((hits (filter pred atoms)))
    (if (null? hits)
        (error "rake-hb-submodules: no atom for" what
               (map expression->string atoms))
        (car hits))))
(define (r8b-in-class cls)
  (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) cls))))
(define (r8b-is-eq f) (eq? (car f) '=))

;; Close (IN w S): unfold the functoid in the GOAL, then sep-mi's two leaves --
;; the VEC(m) typing (TYPE!) and the decomposition existential, whose witnesses
;; are supplied in order and whose atoms are handed to CLOSE!.
(define (r8b-exists! witnesses close!)
  (if (null? witnesses)
      (dk-conj-close! close!)
      (begin
        (ew (car witnesses))
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'FORSOME)
               (r8b-exists! (cdr witnesses) close!)
               (close!)))))))

(define (r8b-mem-in! fld witnesses type! close!)
  (mac fld)
  (for-each
   (lambda (r8b-leaf)
     (dk-focus! r8b-leaf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         (r8b-exists! witnesses close!)
         (type!)))
   (dk-opened (lambda () (sep-mi)))))

;; the standard atom closer for a membership goal: the decomposition equation
;; gets EQ!, every typing is already in the context
(define (r8b-closer eq!)
  (lambda () (if (eq? (car (dk-goal)) '=) (eq!) (ass))))

;; (IN a RR) and (IN b RR) => (IN (+ a b) RR) / (IN (* a b) RR).  `fact' does
;; NOT split a CONJUNCTIVE antecedent, and rr-add-closed / rr-mul-closed state
;; theirs as one AND: have! the conjunction first.
(define (r8b-rr-closed! thm a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR))
         (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact thm a b))

;; The five conjuncts of IS-SUBMODULE, driven.  KIT is a procedure of the
;; peeled goal returning five procedures, each taking the assumptions the
;; conjunct's own peeling landed.  The closure conjuncts all have the goal
;; (IN (OP ...) S); the dispatch is on OP's ACCESSOR, never on a goal shape
;; that sibling branches share.
(define (r8b-submodule-drive! name stmt kit)
  (sp (make-wff stmt))
  (dk-peel!)
  (let* ((r8b-parts (kit (dk-goal)))
         (r8b-sub!  (list-ref r8b-parts 0))
         (r8b-zero! (list-ref r8b-parts 1))
         (r8b-add!  (list-ref r8b-parts 2))
         (r8b-neg!  (list-ref r8b-parts 3))
         (r8b-act!  (list-ref r8b-parts 4)))
    (mac 'is-submodule)
    (dk-conj-close!
     (lambda ()
       (let ((r8b-g (dk-goal)))
         (cond ((eq? (car r8b-g) 'SUBSET) (r8b-sub! '()))
               ((eq? (car r8b-g) 'IN)     (r8b-zero! '()))
               (#t (let* ((r8b-landed (dk-peel!))
                          (r8b-g2 (dk-goal))
                          (r8b-op (car (car (cadr r8b-g2)))))
                     (cond ((eq? r8b-op 'VADD) (r8b-add! r8b-landed))
                           ((eq? r8b-op 'VNEG) (r8b-neg! r8b-landed))
                           ((eq? r8b-op 'ACT)  (r8b-act! r8b-landed))
                           (#t (error "rake-hb-submodules: unexpected conjunct"
                                      (expression->string r8b-g2)))))))))))
  (r8b-check! name))

;; conjunct 1, shared verbatim: S subset VEC(m) because S is a SEP over VEC(m).
(define (r8b-subset! unfold)
  (lambda (ignored)
    (mac 'subset-def)
    (let ((r8b-h (car (dk-peel!))))
      (r8b-mem-open! unfold r8b-h)
      (ass))))

;; (IN r RR) from (IN r (CARR (SCAL mm))): the carrier read-off used BACKWARDS.
;; `subst' takes an in-context quasi-equation in either orientation, so the
;; goal's RR is rewritten down to carr(scal(mm)) and closed from the context.
(define (r8b-real! mm r)
  (let ((r8b-carr (list 'CARR (list 'SCAL mm))))
    (have! (list '== r8b-carr 'RR)
           (lambda () (mac 'nvs-scal-carr) (qrfl)))
    (have! (list 'IN r 'RR)
           (lambda () (subst (list '== 'RR r8b-carr)) (ass)))))

;;; =====================================================================
;;; line-is-submodule -- norm-as-sup-proof.scm:27
;;; The witnesses are single scalars: 0 for vzero, r+s for the sum, (-1)*r for
;;; the negative, r*s for the action.
;;; =====================================================================
(r8b-submodule-drive! 'line-is-submodule
  '(FORALL m (FORALL v
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
        (IS-SUBMODULE m (LINE m v))))))
  (lambda (r8b-goal)
    (let* ((r8b-m   (cadr r8b-goal))
           (r8b-set (caddr r8b-goal))
           (r8b-v   (caddr r8b-set))
           (r8b-in-set (r8b-in-class r8b-set)))
      ;; decompose (IN w (LINE m v)): returns the scalar and w = r.v
      (define (r8b-split-at! hyp)
        (let ((atoms (r8b-mem-open! 'line-unfold hyp)))
          (list (cadr (r8b-atom atoms (r8b-in-class 'RR) "the scalar typing"))
                (r8b-atom atoms r8b-is-eq "the decomposition equation"))))
      (list
       (r8b-subset! 'line-unfold)
       ;; vzero(m) = 0.v
       (lambda (ignored)
         (fact 'module-vzero-in-normed-vector-space-as-module r8b-m)
         (fact 'rr-zero-in)
         (let ((r8b-z (dk-fact! 'nvs-zero-act r8b-m r8b-v)))
           (r8b-mem-in! 'LINE (list 0) (lambda () (ass))
             (r8b-closer (lambda ()
                           (fact 'eq-sym (cadr r8b-z) (caddr r8b-z))
                           (ass))))))
       ;; x + y = (r+s).v
       (lambda (r8b-landed)
         (let* ((r8b-hs (filter r8b-in-set r8b-landed))
                (r8b-xx (cadr (car r8b-hs)))
                (r8b-yy (cadr (cadr r8b-hs)))
                (r8b-dx (r8b-split-at! (car r8b-hs)))
                (r8b-dy (r8b-split-at! (cadr r8b-hs)))
                (r8b-rx (car r8b-dx))
                (r8b-ry (car r8b-dy)))
           (fact 'nvs-vadd-in-vec r8b-m r8b-xx r8b-yy)
           (r8b-rr-closed! 'rr-add-closed r8b-rx r8b-ry)
           (r8b-mem-in! 'LINE (list (list '+ r8b-rx r8b-ry)) (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadr r8b-dx))
                (subst (cadr r8b-dy))
                (dk-fact! 'nvs-act-add-scalars r8b-m r8b-rx r8b-ry r8b-v)
                (ass))))))
       ;; -x = ((-1)*r).v
       (lambda (r8b-landed)
         (let* ((r8b-h  (car (filter r8b-in-set r8b-landed)))
                (r8b-xx (cadr r8b-h))
                (r8b-dx (r8b-split-at! r8b-h))
                (r8b-rx (car r8b-dx)))
           (fact 'module-vneg-type-normed-vector-space-as-module r8b-m r8b-xx)
           (fact 'rr-one-in)
           (fact 'rr-neg-closed 1)
           (r8b-rr-closed! 'rr-mul-closed r8b-neg1 r8b-rx)
           (r8b-mem-in! 'LINE (list (list '* r8b-neg1 r8b-rx)) (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadr r8b-dx))
                (dk-fact! 'nvs-act-vneg r8b-m r8b-rx r8b-v)
                (ass))))))
       ;; r.x = (r*s).v
       (lambda (r8b-landed)
         (let* ((r8b-h  (car (filter r8b-in-set r8b-landed)))
                (r8b-rr (cadr (car (filter (r8b-in-class (list 'CARR (list 'SCAL r8b-m)))
                                           r8b-landed))))
                (r8b-xx (cadr r8b-h))
                (r8b-dx (r8b-split-at! r8b-h))
                (r8b-sx (car r8b-dx)))
           (r8b-real! r8b-m r8b-rr)
           (fact 'nvs-act-in-vec r8b-m r8b-rr r8b-xx)
           (r8b-rr-closed! 'rr-mul-closed r8b-rr r8b-sx)
           (r8b-mem-in! 'LINE (list (list '* r8b-rr r8b-sx)) (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadr r8b-dx))
                (dk-fact! 'nvs-act-scale-assoc r8b-m r8b-rr r8b-sx r8b-v)
                (ass))))))))))

;;; =====================================================================
;;; span-add-one-submodule -- hahn-banach-full-proof.scm:79
;;; The same five conjuncts with a PAIR of witnesses: the t-component and the
;;; scalar.  t's own closure (submodule-vadd-closed / -vneg-closed /
;;; -act-closed) carries the first, and nvs-vadd-shuffle rearranges
;;; (a + r.v) + (b + s.v) into (a + b) + (r+s).v.
;;; =====================================================================
(r8b-submodule-drive! 'span-add-one-submodule
  '(FORALL m (FORALL t (FORALL v
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IS-SUBMODULE m t) (IMPLIES (IN v (VEC m))
        (IS-SUBMODULE m (SPAN-ADD-ONE m t v))))))))
  (lambda (r8b-goal)
    (let* ((r8b-m   (cadr r8b-goal))
           (r8b-set (caddr r8b-goal))
           (r8b-t   (caddr r8b-set))
           (r8b-v   (cadddr r8b-set))
           (r8b-vec (list 'VEC r8b-m))
           (r8b-in-set (r8b-in-class r8b-set)))
      ;; decompose (IN w (SPAN-ADD-ONE m t v)):
      ;;   (list w-in-vec  t-component  scalar  the equation w = a + r.v)
      (define (r8b-split-at! hyp)
        (let ((atoms (r8b-mem-open! 'span-add-one-unfold hyp)))
          (list (r8b-atom atoms (r8b-in-class r8b-vec) "the VEC(m) typing")
                (cadr (r8b-atom atoms (r8b-in-class r8b-t) "the t-component typing"))
                (cadr (r8b-atom atoms (r8b-in-class 'RR) "the scalar typing"))
                (r8b-atom atoms r8b-is-eq "the decomposition equation"))))
      (list
       (r8b-subset! 'span-add-one-unfold)
       ;; vzero(m) = vzero(m) + 0.v
       (lambda (ignored)
         (fact 'module-vzero-in-normed-vector-space-as-module r8b-m)
         (fact 'submodule-vzero-in r8b-m r8b-t)
         (fact 'rr-zero-in)
         (let ((r8b-z (dk-fact! 'nvs-zero-act r8b-m r8b-v)))
           (r8b-mem-in! 'SPAN-ADD-ONE (list (list 'VZERO r8b-m) 0) (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst r8b-z)
                (subst (dk-fact! 'nvs-vzero-right r8b-m (list 'VZERO r8b-m)))
                (rfl))))))
       ;; (a + r.v) + (b + s.v) = (a + b) + (r+s).v
       (lambda (r8b-landed)
         (let* ((r8b-hs (filter r8b-in-set r8b-landed))
                (r8b-xx (cadr (car r8b-hs)))
                (r8b-yy (cadr (cadr r8b-hs)))
                (r8b-dx (r8b-split-at! (car r8b-hs)))
                (r8b-dy (r8b-split-at! (cadr r8b-hs)))
                (r8b-ax (cadr r8b-dx)) (r8b-rx (caddr r8b-dx))
                (r8b-ay (cadr r8b-dy)) (r8b-ry (caddr r8b-dy))
                (r8b-px (list (list 'ACT r8b-m) r8b-rx r8b-v))
                (r8b-py (list (list 'ACT r8b-m) r8b-ry r8b-v)))
           ;; the t-components are vectors
           (let ((r8b-sub (dk-fact! 'submodule-subset r8b-m r8b-t)))
             (dk-fact! 'subset-mem-fwd r8b-t r8b-vec r8b-ax)
             (dk-fact! 'subset-mem-fwd r8b-t r8b-vec r8b-ay))
           (fact 'nvs-act-in-vec r8b-m r8b-rx r8b-v)
           (fact 'nvs-act-in-vec r8b-m r8b-ry r8b-v)
           (fact 'nvs-vadd-in-vec r8b-m r8b-xx r8b-yy)
           (r8b-rr-closed! 'rr-add-closed r8b-rx r8b-ry)
           (dk-apply! (dk-fact! 'submodule-vadd-closed r8b-m r8b-t) r8b-ax r8b-ay)
           (r8b-mem-in! 'SPAN-ADD-ONE
             (list (list (list 'VADD r8b-m) r8b-ax r8b-ay) (list '+ r8b-rx r8b-ry))
             (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadddr r8b-dx))
                (subst (cadddr r8b-dy))
                (subst (dk-fact! 'nvs-vadd-shuffle r8b-m r8b-ax r8b-ay r8b-px r8b-py))
                (subst (dk-fact! 'nvs-act-add-scalars r8b-m r8b-rx r8b-ry r8b-v))
                (fact 'nvs-vadd-in-vec r8b-m r8b-ax r8b-ay)
                (fact 'nvs-act-in-vec r8b-m (list '+ r8b-rx r8b-ry) r8b-v)
                (fact 'nvs-vadd-in-vec r8b-m
                      (list (list 'VADD r8b-m) r8b-ax r8b-ay)
                      (list (list 'ACT r8b-m) (list '+ r8b-rx r8b-ry) r8b-v))
                (rfl))))))
       ;; -(a + r.v) = (-a) + ((-1)*r).v
       (lambda (r8b-landed)
         (let* ((r8b-h  (car (filter r8b-in-set r8b-landed)))
                (r8b-xx (cadr r8b-h))
                (r8b-dx (r8b-split-at! r8b-h))
                (r8b-ax (cadr r8b-dx)) (r8b-rx (caddr r8b-dx))
                (r8b-px (list (list 'ACT r8b-m) r8b-rx r8b-v)))
           (dk-fact! 'submodule-subset r8b-m r8b-t)
           (dk-fact! 'subset-mem-fwd r8b-t r8b-vec r8b-ax)
           (fact 'nvs-act-in-vec r8b-m r8b-rx r8b-v)
           (fact 'module-vneg-type-normed-vector-space-as-module r8b-m r8b-xx)
           (fact 'rr-one-in)
           (fact 'rr-neg-closed 1)
           (r8b-rr-closed! 'rr-mul-closed r8b-neg1 r8b-rx)
           (dk-apply! (dk-fact! 'submodule-vneg-closed r8b-m r8b-t) r8b-ax)
           (r8b-mem-in! 'SPAN-ADD-ONE
             (list (list (list 'VNEG r8b-m) r8b-ax) (list '* r8b-neg1 r8b-rx))
             (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadddr r8b-dx))
                (subst (dk-fact! 'nvs-vneg-vadd r8b-m r8b-ax r8b-px))
                (subst (dk-fact! 'nvs-act-vneg r8b-m r8b-rx r8b-v))
                (fact 'module-vneg-type-normed-vector-space-as-module r8b-m r8b-ax)
                (fact 'nvs-act-in-vec r8b-m (list '* r8b-neg1 r8b-rx) r8b-v)
                (fact 'nvs-vadd-in-vec r8b-m
                      (list (list 'VNEG r8b-m) r8b-ax)
                      (list (list 'ACT r8b-m) (list '* r8b-neg1 r8b-rx) r8b-v))
                (rfl))))))
       ;; r.(a + s.v) = r.a + (r*s).v
       (lambda (r8b-landed)
         (let* ((r8b-h  (car (filter r8b-in-set r8b-landed)))
                (r8b-rr (cadr (car (filter (r8b-in-class (list 'CARR (list 'SCAL r8b-m)))
                                           r8b-landed))))
                (r8b-xx (cadr r8b-h))
                (r8b-dx (r8b-split-at! r8b-h))
                (r8b-ax (cadr r8b-dx)) (r8b-sx (caddr r8b-dx))
                (r8b-px (list (list 'ACT r8b-m) r8b-sx r8b-v)))
           (r8b-real! r8b-m r8b-rr)
           (dk-fact! 'submodule-subset r8b-m r8b-t)
           (dk-fact! 'subset-mem-fwd r8b-t r8b-vec r8b-ax)
           (fact 'nvs-act-in-vec r8b-m r8b-sx r8b-v)
           (fact 'nvs-act-in-vec r8b-m r8b-rr r8b-xx)
           (r8b-rr-closed! 'rr-mul-closed r8b-rr r8b-sx)
           (dk-apply! (dk-fact! 'submodule-act-closed r8b-m r8b-t) r8b-rr r8b-ax)
           (r8b-mem-in! 'SPAN-ADD-ONE
             (list (list (list 'ACT r8b-m) r8b-rr r8b-ax) (list '* r8b-rr r8b-sx))
             (lambda () (ass))
             (r8b-closer
              (lambda ()
                (subst (cadddr r8b-dx))
                (subst (dk-fact! 'nvs-act-distrib-vec r8b-m r8b-rr r8b-ax r8b-px))
                (subst (dk-fact! 'nvs-act-scale-assoc r8b-m r8b-rr r8b-sx r8b-v))
                (fact 'nvs-act-in-vec r8b-m r8b-rr r8b-ax)
                (fact 'nvs-act-in-vec r8b-m (list '* r8b-rr r8b-sx) r8b-v)
                (fact 'nvs-vadd-in-vec r8b-m
                      (list (list 'ACT r8b-m) r8b-rr r8b-ax)
                      (list (list 'ACT r8b-m) (list '* r8b-rr r8b-sx) r8b-v))
                (rfl))))))))))
