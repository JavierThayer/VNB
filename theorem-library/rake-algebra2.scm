;;; rake-algebra2.scm -- BATCH I of the 2026-09-17 rake: the algebra two-liners
;;; and the four unwarranted algebra axioms, PROVEN.  Every statement is its
;;; site's statement UNCHANGED (extracted from the site, not retyped).
;;;
;;;   abelian-group-assoc         structure-library/abelian-group.scm:77   (support)
;;;   abelian-group-right-id      structure-library/abelian-group.scm:64   (support)
;;;   abelian-group-inverse-unique structure-library/abelian-group.scm:47  (support)
;;;   ring-add-right-inv          structure-library/matrix.scm:367         (support)
;;;   ring-neg-neg                structure-library/mat-equiv.scm:31       (support)
;;;   ring-neg-mul-left           structure-library/ring.scm:105           (support)
;;;   matrix-sethood              structure-library/matrix.scm:80          (add-axiom!)
;;;   monoid-identity-in          structure-library/monoid.scm:40          (add-axiom!)
;;;   monoid-carrier-closed-opr   structure-library/monoid.scm:45          (add-axiom!)
;;;   mpow-type                   structure-library/monoid-power.scm:43    (add-axiom!)
;;;
;;; Two auxiliary theorems are installed beside them:
;;;   ring-add-inverse-unique  a + b = 0 => b = -a in any ring.  The ring twin
;;;                            of abelian-group-inverse-unique, proved directly
;;;                            from the four additive ring laws rather than
;;;                            through the RING-ADDITIVE-AG view (the view's
;;;                            NEG/INV read-off does not exist).  ring-neg-neg
;;;                            and ring-neg-mul-left are both one citation of it.
;;;   mpow-type-ind            mpow-type with the EXPONENT OUTERMOST, so that
;;;                            `ni' fires (it tests the goal's SHAPE, and the
;;;                            support quantifies the monoid first).
;;;
;;; THE SHAPES.  Nothing here has content beyond its statement:
;;;   * abelian-group-* : `abelian-group-is-group' plus the matching GROUP
;;;     projection (all six PROVEN in structure-library/subtype-laws.scm), one
;;;     `subst' where the left/right side has to be flipped by
;;;     abelian-group-opr-comm.  inverse-unique cancels on the left
;;;     (group-cancel-left, theorem-library/cancellation.scm) against
;;;     a*b = e = a*a^{-1}.
;;;   * ring-add-right-inv : ring-add-comm then ring-add-left-inv, exactly the
;;;     ring-add-right-id shape of theorem-library/rake-algebra.scm.
;;;   * ring-add-inverse-unique : b = 0+b = ((-a)+a)+b = (-a)+(a+b) = (-a)+0 = -a,
;;;     five `subst's down the chain and `rfl'.
;;;   * ring-neg-mul-left : a*b + (-a)*b = (a + -a)*b = 0*b = 0 in a `have!' lane
;;;     (ring-right-dist reversed, ring-add-right-inv, ring-mul-zero-left), then
;;;     ring-add-inverse-unique.
;;;   * matrix-sethood : MATRIX(X) is a subclass of the set TUPLES(TUPLES X) --
;;;     matrix-membership's first conjunct -- so tuples-sethood twice and
;;;     subclass-of-set-is-set.  theorem-library/rake-mat-typing.scm's mat-is-set
;;;     does the same thing inline, which is why it did NOT have to cite this
;;;     axiom.
;;;   * the two monoid projections : theorem-library/op-typing.scm's driver at
;;;     IS-MONOID -- unfold, split, and for OPR bridge the TUPLING with
;;;     apply-tupling-2 (a `==', which `subst' takes) before fun-apply-type-c.
;;;     They are the MONOID twins of comm-monoid-carrier-closed-opr /
;;;     comm-monoid-identity-in-carr (theorem-library/rake-finsum-typing.scm),
;;;     which were proved there precisely BECAUSE these two were unwarranted
;;;     axioms; now they are not.
;;;   * mpow-type : NN induction on the exponent, base mpow-zero, step
;;;     mpow-succ + monoid-carrier-closed-opr.  Same induction as
;;;     rake-finsum-typing.scm's mpow-comm-monoid-type-ind, lifted from
;;;     COMM-MONOID to MONOID.  monoid-carrier-closed-opr's antecedent is one
;;;     CONJUNCTION, which `fact' will not split, so it is assembled by
;;;     `have!' + `prop' before the citation.
;;;
;;; THE VIEW COMPANIONS -- the one thing in this file that is not a proof.
;;; `view-as-auto-specialize!' runs inside `def-functor', i.e. when views.scm
;;; loads (position 60), so a theorem proved HERE is invisible to it and its
;;; companions are never built.  The three abelian-group supports were visible
;;; there (abelian-group.scm is position 22), and FOUR proofs cite the resulting
;;; MODULE-VECTOR-AG companions BY NAME:
;;;
;;;   abelian-group-inverse-unique-module-vector-ag  span-bricks-proof.scm:123
;;;   abelian-group-right-id-module-vector-ag        lastcoeff-ideal-proof.scm:78, :417
;;;   abelian-group-assoc-module-vector-ag           lastcoeff-ideal-proof.scm:402
;;;
;;; Retiring the supports without rebuilding them deletes those three names and
;;; breaks both files.  The three RESTRICTED re-runs at the foot of this file
;;; rebuild exactly those three and nothing else (the unrestricted form would
;;; install every abelian-group theorem proved since views.scm).  This is
;;; theorem-library/cancellation.scm:186's move, for the same reason.
;;; The other companions of these ten names (the ring-additive-ag /
;;; field-additive-ag / normed-ag chains, monoid-identity-in's twelve,
;;; mpow-type's two) are cited by NO .scm file in the tree and are not rebuilt
;;; here; see the batch report.
;;;
;;; LOAD WINDOW [226, 241) -- the file may occupy any slot in it.
;;;   lo = 226: the latest citation is `ring-add-right-id', which is PROVEN in
;;;             theorem-library/rake-algebra (position 225), so this file has to
;;;             come after it.  Next latest are
;;;             ring-mul-zero-left (ring-zero-one-power, 210), group-inv-in and
;;;             group-cancel-left (cancellation, 209), ring-neg-in-carr and
;;;             ring-carrier-closed-mul (op-typing, 199), the six group
;;;             projections (subtype-laws, 198), subclass-of-set-is-set
;;;             (subset-lemmas, 193), pair-in-cartesian (pair-tuple-sethood,
;;;             165), fun-apply-type-c (fun-apply-type-proof, 163), eq-sym
;;;             (equality-basics, 148).
;;;   hi = 241: theorem-library/rake-mat-typing cites `mpow-type' (:671).  The
;;;             other earliest citers are all later: ring-add-right-inv 336
;;;             (elem-inverses-proof), ring-neg-neg 341 (mat-equiv-proof),
;;;             abelian-group-inverse-unique 357 (span-bricks-proof, through its
;;;             companion), abelian-group-right-id / abelian-group-assoc /
;;;             ring-neg-mul-left 359 (lastcoeff-ideal-proof); matrix-sethood,
;;;             monoid-identity-in and monoid-carrier-closed-opr have no citer
;;;             in the tree at all.
;;;
;;; Helper prefix `rki-'.  All helpers are file-local.

(define (rki-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rki: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rki: proof not complete" name))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (rki-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rki-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rki-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

(define (rki-pick-head head what) (dk-pick (dk-head? head) what))

;; the NN-typed eigenvariable in context: (IN v NN) with v a symbol.
(define (rki-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN)))
                 "n in NN")))

;;; =====================================================================
;;; abelian-group-assoc -- group-assoc through abelian-group-is-group.
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (FORALL c (IMPLIES (IN c (CARR s))
           (= ((OPR s) ((OPR s) a b) c) ((OPR s) a ((OPR s) b c)))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-assoc 's 'a 'b 'c)
(ass)
(rki-check! 'abelian-group-assoc)
(qed 'abelian-group-assoc)
(topic! 'abelian-group-assoc 'algebra)

;;; =====================================================================
;;; abelian-group-right-id -- a*e = e*a = a.
;;; =====================================================================
(sp (make-wff
 '(FORALL s
     (IMPLIES (IS-ABELIAN-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((OPR s) a (IDEN s)) a)))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-identity-in 's)
(fact 'abelian-group-opr-comm 's 'a '(IDEN s))
(fact 'group-left-id 's 'a)
(subst '(= ((OPR s) a (IDEN s)) ((OPR s) (IDEN s) a)))
(ass)
(rki-check! 'abelian-group-right-id)
(qed 'abelian-group-right-id)
(topic! 'abelian-group-right-id 'algebra)

;;; =====================================================================
;;; abelian-group-inverse-unique -- a*b = e forces b = a^{-1}.
;;; a*b = e = a^{-1}*a = a*a^{-1} (commutativity), then cancel a on the left.
;;; The `have!' lane builds the equation group-cancel-left wants; the warrant's
;;; own route (b = e*b = (a^{-1}*a)*b = ...) is that cancellation spelled out.
;;; =====================================================================
(sp (make-wff
 '(FORALL s
     (IMPLIES (IS-ABELIAN-GROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (IMPLIES (= ((OPR s) a b) (IDEN s))
             (= b ((INV s) a)))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-inv-in 's 'a)
(fact 'group-left-inv 's 'a)
(fact 'abelian-group-opr-comm 's 'a '((INV s) a))
(have! '(= ((OPR s) a b) ((OPR s) a ((INV s) a)))
  (lambda ()
    (subst '(= ((OPR s) a b) (IDEN s)))
    (subst '(= ((OPR s) a ((INV s) a)) ((OPR s) ((INV s) a) a)))
    (subst '(= ((OPR s) ((INV s) a) a) (IDEN s)))
    (rfl)))
(dk-focus-having! '(= ((OPR s) a b) ((OPR s) a ((INV s) a))))
(fact 'group-cancel-left 's 'b '((INV s) a) 'a)
(ass)
(rki-check! 'abelian-group-inverse-unique)
(qed 'abelian-group-inverse-unique)
(topic! 'abelian-group-inverse-unique 'algebra)

;;; =====================================================================
;;; ring-add-right-inv -- a + (-a) = 0.
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s)) (= ((ADD s) a ((NEG s) a)) (ZERO s))))))))
(dk-peel!)
(fact 'ring-neg-in-carr 's 'a)
(fact 'ring-add-comm 's 'a '((NEG s) a))
(fact 'ring-add-left-inv 's 'a)
(subst '(= ((ADD s) a ((NEG s) a)) ((ADD s) ((NEG s) a) a)))
(ass)
(rki-check! 'ring-add-right-inv)
(qed 'ring-add-right-inv)
(topic! 'ring-add-right-inv 'algebra)

;;; =====================================================================
;;; ring-add-inverse-unique (AUX) -- a + b = 0 forces b = -a.
;;;   b = 0 + b = ((-a) + a) + b = (-a) + (a + b) = (-a) + 0 = -a.
;;; Everything cited is definitional (the additive ring laws) except
;;; ring-add-right-id (PROVEN, theorem-library/rake-algebra.scm) and
;;; ring-neg-in-carr (PROVEN, theorem-library/op-typing.scm).
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (IMPLIES (= ((ADD s) a b) (ZERO s))
                  (= b ((NEG s) a)))))))))))
(dk-peel!)
(fact 'ring-neg-in-carr 's 'a)
(fact 'ring-add-left-id 's 'b)
(fact 'ring-add-left-inv 's 'a)
(fact 'ring-add-assoc 's '((NEG s) a) 'a 'b)
(fact 'ring-add-right-id 's '((NEG s) a))
(subst '(= b ((ADD s) (ZERO s) b)))
(subst '(= (ZERO s) ((ADD s) ((NEG s) a) a)))
(subst '(= ((ADD s) ((ADD s) ((NEG s) a) a) b) ((ADD s) ((NEG s) a) ((ADD s) a b))))
(subst '(= ((ADD s) a b) (ZERO s)))
(subst '(= ((ADD s) ((NEG s) a) (ZERO s)) ((NEG s) a)))
(rfl)
(rki-check! 'ring-add-inverse-unique)
(qed 'ring-add-inverse-unique)
(gloss! 'ring-add-inverse-unique
  "In a ring, an element b with a + b = 0 IS the additive inverse of a.  The
   ring twin of abelian-group-inverse-unique; cite it to identify a computed
   element as a negation.")
(topic! 'ring-add-inverse-unique 'algebra)

;;; =====================================================================
;;; ring-neg-neg -- -(-r) = r.  r is an additive inverse of -r
;;; (ring-add-left-inv at r), and inverses are unique.
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-RING s) (FORALL r (IMPLIES (IN r (CARR s))
     (= ((NEG s) ((NEG s) r)) r)))))))
(dk-peel!)
(fact 'ring-neg-in-carr 's 'r)
(fact 'ring-add-left-inv 's 'r)
(fact 'ring-add-inverse-unique 's '((NEG s) r) 'r)
(fact 'eq-sym 'r '((NEG s) ((NEG s) r)))
(ass)
(rki-check! 'ring-neg-neg)
(qed 'ring-neg-neg)
(topic! 'ring-neg-neg 'algebra)

;;; =====================================================================
;;; ring-neg-mul-left -- (-a)*b = -(a*b).
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (= ((MUL s) ((NEG s) a) b) ((NEG s) ((MUL s) a b)))))))))))
(dk-peel!)
(fact 'ring-neg-in-carr 's 'a)
(fact 'ring-carrier-closed-mul 's 'a 'b)
(fact 'ring-carrier-closed-mul 's '((NEG s) a) 'b)
(fact 'ring-add-right-inv 's 'a)
(fact 'ring-mul-zero-left 's 'b)
(fact 'ring-right-dist 's 'a '((NEG s) a) 'b)
(have! '(= ((ADD s) ((MUL s) a b) ((MUL s) ((NEG s) a) b)) (ZERO s))
  (lambda ()
    (subst '(= ((ADD s) ((MUL s) a b) ((MUL s) ((NEG s) a) b))
               ((MUL s) ((ADD s) a ((NEG s) a)) b)))
    (subst '(= ((ADD s) a ((NEG s) a)) (ZERO s)))
    (ass)))
(dk-focus-having! '(= ((ADD s) ((MUL s) a b) ((MUL s) ((NEG s) a) b)) (ZERO s)))
(fact 'ring-add-inverse-unique 's '((MUL s) a b) '((MUL s) ((NEG s) a) b))
(ass)
(rki-check! 'ring-neg-mul-left)
(qed 'ring-neg-mul-left)
(topic! 'ring-neg-mul-left 'algebra)

;;; =====================================================================
;;; matrix-sethood -- MATRIX(X) is a set when X is.
;;; =====================================================================
(sp (make-wff '(FORALL S (IMPLIES (IN S SET) (IN (MATRIX S) SET)))))
(dk-peel!)
(fact 'tuples-sethood 'S)
(fact 'tuples-sethood '(TUPLES S))
(have! '(SUBSET (MATRIX S) (TUPLES (TUPLES S)))
  (lambda ()
    (mac 'subset-def)
    (let ((h (dk-landed-1 (lambda () (di)))))
      (dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership h))))
      (ass))))
(dk-focus-having! '(SUBSET (MATRIX S) (TUPLES (TUPLES S))))
(fact 'subclass-of-set-is-set '(MATRIX S) '(TUPLES (TUPLES S)))
(ass)
(rki-check! 'matrix-sethood)
(qed 'matrix-sethood)
(topic! 'matrix-sethood 'algebra)

;;; =====================================================================
;;; monoid-identity-in -- the `constant IDEN CARR' slot's membership conjunct.
;;; =====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IS-MONOID m) (IN (IDEN m) (CARR m))))))
(dk-peel!)
(mac-h 'is-monoid '(IS-MONOID m))
(dk-split-all!)
(ass)
(rki-check! 'monoid-identity-in)
(qed 'monoid-identity-in)
(topic! 'monoid-identity-in 'algebra)

;;; =====================================================================
;;; monoid-carrier-closed-opr -- the (op OPR (CARTESIAN CARR CARR) CARR) slot,
;;; in APPLIED form.  The gap is the TUPLING, bridged by apply-tupling-2.
;;; =====================================================================
(sp (make-wff
 '(FORALL m (FORALL a (FORALL b
      (IMPLIES (AND (IS-MONOID m) (AND (IN a (CARR m)) (IN b (CARR m))))
               (IN ((OPR m) a b) (CARR m))))))))
(dk-peel!)
(dk-split-all!)
(mac-h 'is-monoid '(IS-MONOID m))
(dk-split-all!)
(fact 'apply-tupling-2 '(OPR m) 'a 'b)
(subst '(== ((OPR m) a b) ((OPR m) (LIST a b))))
(fact 'pair-in-cartesian '(CARR m) '(CARR m) 'a 'b)
(fact 'fun-apply-type-c '(OPR m) '(CARTESIAN (CARR m) (CARR m)) '(CARR m) '(LIST a b))
(ass)
(rki-check! 'monoid-carrier-closed-opr)
(qed 'monoid-carrier-closed-opr)
(topic! 'monoid-carrier-closed-opr 'algebra)

;;; =====================================================================
;;; mpow-type-ind (AUX) -- the exponent OUTERMOST, so that `ni' fires.
;;;   base  MPOW(m,x,0) = IDEN(m)                      (mpow-zero)
;;;   step  MPOW(m,x,succ n) = (OPR m)(x, MPOW(m,x,n)) (mpow-succ)
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL m (IMPLIES (IS-MONOID m)
    (FORALL x (IMPLIES (IN x (CARR m))
      (IN (MPOW m x n) (CARR m))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rki-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rki-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (let ((mv (cadr (rki-pick-head 'IS-MONOID "IS-MONOID m"))))
    (mac 'mpow-zero)
    (dk-fact! 'monoid-identity-in mv)
    (ass))
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (rki-nn-var))
         (gl (dk-goal))                          ; (IN (MPOW m x (succ n)) (CARR m))
         (mv (cadr (cadr gl)))
         (xv (caddr (cadr gl)))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH"))
         (guard (list 'AND (list 'IS-MONOID mv)
                      (list 'AND (list 'IN xv (list 'CARR mv))
                            (list 'IN (list 'MPOW mv xv nv) (list 'CARR mv))))))
    (mac 'mpow-succ)
    (dk-apply! ih mv xv)
    ;; monoid-carrier-closed-opr's antecedent is ONE conjunction, which `fact'
    ;; will not split -- assemble it first (CLAUDE.md, "Writing proof drivers").
    (have! guard (lambda () (prop)))
    (dk-focus-having! guard)
    (dk-fact! 'monoid-carrier-closed-opr mv xv (list 'MPOW mv xv nv))
    (ass)))
(rki-check! 'mpow-type-ind)
(qed 'mpow-type-ind)
(gloss! 'mpow-type-ind
  "MPOW(m,x,n) lies in CARR(m), stated with the exponent outermost so that `ni'
   fires on it.  mpow-type is this theorem with the binders in the order the
   library cites them.")
(topic! 'mpow-type-ind 'algebra)

;;; =====================================================================
;;; mpow-type -- the site's own binder order.
;;; =====================================================================
(sp (make-wff
 '(FORALL m
     (IMPLIES (IS-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (FORALL n (IMPLIES (IN n NN)
           (IN (MPOW m x n) (CARR m))))))))))
(dk-peel!)
(fact 'mpow-type-ind 'n 'm 'x)
(ass)
(rki-check! 'mpow-type)
(qed 'mpow-type)
(topic! 'mpow-type 'algebra)

;;; =====================================================================
;;; The three MODULE-VECTOR-AG companions the library cites by name.  See the
;;; header: views.scm built them from the SUPPORTS, and the supports are being
;;; retired.  RESTRICTED to one theorem each on purpose (cancellation.scm:186).
;;; =====================================================================
(view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-assoc)
(view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-right-id)
(view-as-auto-specialize! 'MODULE-VECTOR-AG 'abelian-group-inverse-unique)
