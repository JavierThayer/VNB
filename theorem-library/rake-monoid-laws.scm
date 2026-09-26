;;; rake-monoid-laws.scm -- BATCH 5c-P of the 2026-09-18 rake: the three MONOID
;;; shape projections, PROVEN.
;;;
;;;   monoid-assoc     structure-library/monoid.scm:19   (theory-add-axiom!)
;;;   monoid-left-id   structure-library/monoid.scm:29   (theory-add-axiom!)
;;;   monoid-right-id  structure-library/monoid.scm:36   (theory-add-axiom!)
;;;
;;; Each statement is its site's statement UNCHANGED (copied from the
;;; theory-add-axiom! form, not retyped from a printed goal).
;;;
;;; WHAT THEY ARE.  `declare-structure MONOID' carries
;;;     (property is-associative OPR CARR)
;;;     (property is-identity    OPR IDEN CARR)
;;; so the IS-MONOID shape macete unfolds to a conjunction whose conjuncts are
;;; exactly `(is-associative (OPR s) (CARR s))' and
;;; `(is-identity (OPR s) (IDEN s) (CARR s))'.  Unfolding the first of those
;;; (operation-properties.scm) IS monoid-assoc's body up to alpha; unfolding the
;;; second gives, at each carrier element, the CONJUNCTION of the left and the
;;; right identity law.  So all three are projections in the sense of
;;; structure-library/subtype-laws.scm's `stl--project!', which does exactly this
;;; for GROUP -- `group-assoc' (an untouched whole property, closed by `ass'
;;; alpha-aware) and `group-left-id' (one side of a two-sided property: peel the
;;; element binder, instantiate the unfolded universal at the eigenvariable,
;;; detach its typing guard, split the conjunction).  `r7p-project!' below is that
;;; driver with IS-MONOID in place of IS-GROUP; monoid-right-id is the OTHER
;;; conjunct of the same split, which GROUP never needed.
;;;
;;; WHY IT IS WORTH DOING.  monoid.scm carries no `warrant!' and no provenance
;;; wrap over these three, so they are UNWARRANTED axioms: any bill naming one
;;; reads `trust: none', the weakest report there is, for facts that are literally
;;; conjuncts of the IS-MONOID definition.  Proving them is the same work as a
;;; `definitional' stamp and says more, since the unfold is CHECKED rather than
;;; asserted to exist (CLAUDE.md, "The shape projections").  Two proof files in
;;; the tree already route AROUND them for exactly this reason:
;;; theorem-library/monalg-is-ring.scm's `mir-monoid-id!' rebuilds the identity
;;; laws inline from the IS-MONOID unfold ("monoid-left-id / -right-id are
;;; unwarranted axioms in monoid.scm; the unfold is free"), and
;;; theorem-library/rake-det-small.scm measured a monoid-level `mpow-one', got
;;; `modulo {monoid-right-id} [trust: none]', and declined it in favour of the
;;; ring-level statement.  Both can cite these names once the axioms are retired.
;;;
;;; LOAD WINDOW [140, 528) -- the file may occupy ANY slot in it, and the reason
;;; the window is that wide is measured, not assumed:
;;;   lo = 140, the floor for any proof file: `interactive' (134, sp/di/mac-h/qed),
;;;        `driver-kit' (138, the dk- kit) and `proof-debt' (139, so `qed' can
;;;        bill).  There is NO other citation.  The proofs cite no theorem at all
;;;        -- only two MACETES, the IS-MONOID shape unfold (structure-library/
;;;        monoid.scm, 20) and the `is-associative' / `is-identity' def-predicate
;;;        unfolds (structure-library/operation-properties.scm, 14) -- both far
;;;        below the floor.
;;;   hi = 528 (end of the load): NOTHING in the tree cites monoid-assoc,
;;;        monoid-left-id or monoid-right-id, and nothing cites any of their six
;;;        view companions either.  No bill in reference/PROOF-DEBT.md names one.
;;;        Measured by grep over structure-library/, theorem-library/, calculus/
;;;        and the root: the only occurrences of the three names outside
;;;        monoid.scm are COMMENTS, in the two files named above plus
;;;        theorem-library/rake-finsum-core.scm, theorem-library/monalg-laws.scm
;;;        and structure-library/sequences.scm (the latter two describing
;;;        derivations nobody ran).  Placing it beside the other rake algebra
;;;        files (after theorem-library/rake-algebra2, 229) is the natural slot.
;;;
;;; THE VIEW COMPANIONS, AND THERE ARE 363 OF THEM.  `view-as-auto-specialize!'
;;; runs inside `def-functor', i.e. when structure-library/views.scm loads
;;; (position 60) and again at every later `def-functor'.  monoid.scm is position
;;; 20, so all three axioms were visible to the specializer, and each companion
;;; is itself in the theorem table when the NEXT view loads -- so the companions
;;; CHAIN.  Measured on the band: 366 installed names begin with one of the three
;;; law names (the 3 laws + 363 companions; 39 of the 366 carry no `-rev'
;;; segment, i.e. 3 laws + 36 forward companions, each law contributing twelve):
;;;   monoid-<law>-ring-multiplicative-monoid                      (views.scm:41)
;;;   monoid-<law>-abelian-group-as-monoid                         (views.scm:58)
;;;   ...-abelian-group-as-monoid-ring-additive-ag
;;;   ...-abelian-group-as-monoid-commutative-ring-additive-ag
;;;   ...-abelian-group-as-monoid-commutative-ring-additive-ag-normed-field-as-commutative-ring
;;;   ...-abelian-group-as-monoid-field-additive-ag
;;;   ...-abelian-group-as-monoid-normed-field-additive-ag
;;;   ...-abelian-group-as-monoid-module-vector-ag
;;;   ...-abelian-group-as-monoid-module-vector-ag-normed-vector-space-as-module
;;;   ...-abelian-group-as-monoid-module-vector-ag-complex-inner-product-space-as-module
;;;   ...-abelian-group-as-monoid-normed-ag-as-abelian-group
;;;   ...-abelian-group-as-monoid-normed-ag-as-abelian-group-normed-vector-space-as-normed-ag
;;; plus the `-rev' of each and the companions of those.
;;;
;;; NO .scm file in the tree cites ANY of the 366 by name (grep over
;;; structure-library/, theorem-library/, calculus/, emacs/ and the root,
;;; test-suite.scm included).  So retiring the three axioms deletes 366 names
;;; nobody uses, and NO restricted `view-as-auto-specialize!' re-run is needed
;;; here -- unlike theorem-library/rake-algebra2.scm, where three
;;; MODULE-VECTOR-AG companions WERE cited by name and had to be rebuilt.  Two
;;; things follow for the integrator.  (1) The cold load's theorem count drops by
;;; 366 (4593 -> 4227 on the evening band); that is the expected number, not a
;;; regression.  (2) The chain CANNOT be rebuilt from here even if someone wanted
;;; it: the companions of the companions exist only because each `def-functor'
;;; saw the previous view's output, and every `def-functor' in the tree has run
;;; long before any proof file can load.  A proof file cannot sit above
;;; `interactive' (134), so this is a property of proving a structure law at all,
;;; not of this file's position.
;;;
;;; Helper prefix `r7p-'.  All helpers are file-local.

;;; --- local helpers ------------------------------------------------------

(define (r7p-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7p: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ")
                    (display (expression->string (dk-goal-of l)))
                    (newline))
                  (proof-leaves))
        (error "r7p: proof not complete" name))))

;; the unique context assumption whose head is HEAD.
(define (r7p-hyp head what) (dk-pick (dk-head? head) what))

;; Project one law out of the IS-MONOID unfold.
;;   GOAL      the support's statement, verbatim.
;;   PROPNAME  the operation-property to unfold (is-associative / is-identity).
;;   SIDE      #f  the goal IS the unfolded property up to alpha (assoc);
;;             'left / 'right  the goal is ONE conjunct of the two-sided
;;             property, so peel the element binder, instantiate, detach the
;;             typing guard and split.
;; Every landed formula is taken by DIFF (dk-landed-1 / dk-split!), never named
;; by shape: the eigenvariable is whatever `di' chose.
(define (r7p-project! name goal propname side)
  (sp (make-wff goal))
  (di) (di)
  (mac-h 'is-monoid (r7p-hyp 'IS-MONOID "the IS-MONOID hypothesis"))
  (dk-split-all!)
  (let ((unfolded (dk-landed-1
                   (lambda () (mac-h propname (r7p-hyp propname
                                                       "the operation-property conjunct"))))))
    (if side
        (let* ((typing (dk-landed-1 (lambda () (di))))        ; (IN a (CARR s))
               (elt    (cadr typing))
               (inst-d (dk-landed-1 (lambda () (inst unfolded elt))))
               (both   (dk-landed-1 (lambda () (detach! inst-d)))))
          (dk-split! both))))
  (ass)
  (r7p-check! name)
  (qed name)
  (topic! name 'algebra))

;;; =====================================================================
;;; monoid-assoc -- the whole `is-associative OPR CARR' property.
;;; =====================================================================
(r7p-project! 'monoid-assoc
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((OPR s) ((OPR s) a b) c)
                ((OPR s) a ((OPR s) b c)))))))))))
  'is-associative #f)

;;; =====================================================================
;;; monoid-left-id -- the LEFT conjunct of `is-identity OPR IDEN CARR'.
;;; =====================================================================
(r7p-project! 'monoid-left-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((OPR s) (IDEN s) a) a)))))
  'is-identity 'left)

;;; =====================================================================
;;; monoid-right-id -- the RIGHT conjunct of the same property.
;;; =====================================================================
(r7p-project! 'monoid-right-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((OPR s) a (IDEN s)) a)))))
  'is-identity 'right)
