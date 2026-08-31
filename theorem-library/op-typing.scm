;;; op-typing.scm -- the codomain typing of a structure operation, in APPLIED
;;; form, PROVEN.  One driver, seven theorems.
;;;
;;; Every `declare-structure' op-clause -- (op MUL (CARTESIAN CARR CARR) CARR),
;;; (op DIST (CARTESIAN PTS PTS) RR) -- becomes a conjunct of the generated
;;; IS-X iff saying the operation lies in a FUN set.  What every proof actually
;;; needs is that conjunct read in APPLIED form: `((MUL r) a b) in CARR(r)'.
;;; Seven such facts were asserted, one per structure and operation, each with a
;;; warrant that recited the same derivation:
;;;
;;;     "From (op MUL (CARTESIAN CARR CARR) CARR) + fun-apply."   (ring.scm)
;;;     "Codomain typing of the metric op."                       (metric-space.scm)
;;;     "the shape conjunct ... read in applied form."            (directional-derivative.scm)
;;;
;;; The derivation was named in the tree in May 2026 -- the apply-tupling
;;; convention note says in as many words that "per-structure closure axioms
;;; become derivable shortcuts via IS-X unfold + the typing conjunct +
;;; binary-apply-type" -- and then nobody ran it.  `binary-apply-type' itself was
;;; never installed; it is not needed, because the two pieces it would have been
;;; built from are both here already.
;;;
;;; THE DRIVER, and why it is four steps and not one.  The gap between the
;;; op-clause and the applied form is the TUPLING: a structure operation is a
;;; function on a CARTESIAN product, so it eats one pair, while the parser emits
;;; the curried `(f a b)'.  `apply-tupling-2' (primitive) is the bridge, and it
;;; is stated with QUASI-equality -- both sides are undefined when f is not
;;; tuple-typed, and `=' would fail there, `=' being the definedness predicate.
;;; `subst' takes a `==' as happily as a `=' (pi-eq-subst!), so the bridge is one
;;; rewrite of the GOAL, after which `pair-in-cartesian' and `fun-apply-type-c'
;;; finish.  Unary operations (NEG, VNRM) skip the tupling entirely.
;;;
;;; WHAT IS NOT HERE.  `nvs-act-in-vec' (scalar action) has the same shape and
;;; does NOT fall to this driver: ACT's domain in the NVS declaration is not
;;; CARTESIAN(RR, VEC(m)) but the scalar ring's carrier, so the pair does not
;;; type without the normed-field-as-commutative-ring view its own warrant
;;; names.  Left asserted, deliberately -- 5 dependents, sole leaf of none.
;;;
;;; PLACEMENT.  After fun-apply-type-proof (fun-apply-type-c) and
;;; pair-tuple-sethood (pair-in-cartesian), and before the earliest citer of any
;;; of the seven, which is compact-separable-proof.  The seven `support' forms
;;; are gone from their home files (ring.scm, metric-space.scm, matrix.scm,
;;; binomial.scm, hahn-banach-full-proof.scm, directional-derivative.scm), all
;;; of which either load before this file or cite nothing until long after it.

;;; ---- the driver (the `ot-' prefix: file-local) ------------------------

;; Peel the FORALL/IMPLIES prefix down to the membership goal.  Guarded on a
;; step count rather than on `di' returning something: `di' is greedy and a
;; count of calls is not a way to land on a chosen goal (CLAUDE.md).
(define (ot-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

;; STMT      the theorem, exactly as its `support' spelled it
;; PRED-NAME the defining iff to unfold  (a NAME, so `mac-h' can rebuild it)
;; PRED-FORM that predicate applied, as it sits in the context
;; OP        the operation term, e.g. (MUL r)
;; ARGS      its arguments, one or two
;; DOMS      the domain of each argument
;; COD       the codomain
;; PRE       optional: run after peeling, before the unfold (subtype descent)
(define (ot-prove! name stmt pred-name pred-form op args doms cod #!optional pre)
  (sp (make-wff stmt))
  (ot-peel!)
  (if (not (default-object? pre)) (pre))
  (mac-h pred-name pred-form)
  (dk-split! (car (dk-asms)))
  (if (= 1 (length args))
      (begin (fact 'fun-apply-type-c op (car doms) cod (car args))
             (ass))
      (let* ((a (car args)) (b (cadr args))
             (lst  (list 'LIST a b))
             (cart (list 'CARTESIAN (car doms) (cadr doms))))
        (fact 'apply-tupling-2 op a b)
        (subst (list '== (cons op args) (list op lst)))   ; == rewrites too
        (fact 'pair-in-cartesian (car doms) (cadr doms) a b)
        (fact 'fun-apply-type-c op cart cod lst)
        (ass)))
  (qed name))

;;; ---- the seven -------------------------------------------------------

(ot-prove! 'ring-add-closed
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (IN ((ADD s) a b) (CARR s))))))))
  'is-ring '(IS-RING s) '(ADD s) '(a b) '((CARR s) (CARR s)) '(CARR s))
(topic! 'ring-add-closed 'algebra)

(ot-prove! 'ring-carrier-closed-mul
  '(FORALL r (IMPLIES (IS-RING r)
     (FORALL a (IMPLIES (IN a (CARR r))
       (FORALL b (IMPLIES (IN b (CARR r))
         (IN ((MUL r) a b) (CARR r))))))))
  'is-ring '(IS-RING r) '(MUL r) '(a b) '((CARR r) (CARR r)) '(CARR r))
(topic! 'ring-carrier-closed-mul 'algebra)

(ot-prove! 'ring-neg-in-carr
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (IN ((NEG s) a) (CARR s))))))
  'is-ring '(IS-RING s) '(NEG s) '(a) '((CARR s)) '(CARR s))
(topic! 'ring-neg-in-carr 'algebra)

;; The commutative ring descends to its ring first -- the op-clause lives in
;; IS-RING, not in the subtype predicate.
(ot-prove! 'bt-add-in-carr
  '(FORALL r (IMPLIES (IS-COMMUTATIVE-RING r)
     (FORALL a (IMPLIES (IN a (CARR r))
       (FORALL b (IMPLIES (IN b (CARR r))
         (IN ((ADD r) a b) (CARR r))))))))
  'is-ring '(IS-RING r) '(ADD r) '(a b) '((CARR r) (CARR r)) '(CARR r)
  (lambda () (fact 'commutative-ring-is-ring 'r)))
(topic! 'bt-add-in-carr 'algebra)

(ot-prove! 'metric-dist-real
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (IN ((DIST s) x y) RR)))))))
  'is-metric-space '(IS-METRIC-SPACE s) '(DIST s) '(x y)
  '((PTS s) (PTS s)) 'RR)
(topic! 'metric-dist-real 'analysis)

(ot-prove! 'vnrm-real
  '(FORALL m (FORALL w_
     (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN w_ (VEC m))
       (IN ((VNRM m) w_) RR)))))
  'is-normed-vector-space '(IS-NORMED-VECTOR-SPACE m) '(VNRM m) '(w_)
  '((VEC m)) 'RR)
(topic! 'vnrm-real 'analysis)

(ot-prove! 'nvs-vadd-in-vec
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (FORALL y_ (IMPLIES (IN y_ (VEC m))
         (IN ((VADD m) x_ y_) (VEC m))))))))
  'is-normed-vector-space '(IS-NORMED-VECTOR-SPACE m) '(VADD m) '(x_ y_)
  '((VEC m) (VEC m)) '(VEC m))
(topic! 'nvs-vadd-in-vec 'analysis)
