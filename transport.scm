;;; transport.scm -- TRANSPORTABLE FACTS.
;;;
;;; A law proved once in a structure, delivered at an instance, IN THE SURFACE
;;; LANGUAGE.
;;;
;;; The problem.  `group-cancel-right' is a fact about groups:
;;;
;;;     forall s. IS-GROUP(s) => forall a,b,c in CARR(s).
;;;                                (OPR s)(a,c) = (OPR s)(b,c) => a = b
;;;
;;; and additive cancellation on the integers IS that fact -- ZZ-RING's additive
;;; group is [ZZ, binplus, 0, binneg] and binplus(x,y) IS x + y (binplus-apply).
;;; But nothing in the tree could get from one to the other, so cancellation on
;;; NN was proved AGAIN, by induction, from Peano axioms it did not need.  That
;;; is the bulk this file exists to stop.
;;;
;;; Three mechanisms existed and none of them met:
;;;
;;;   1. specialize-structure (structures.scm) rewrites a theorem generic in `s'
;;;      into a theorem about ZZ-RING.  It works, it is tested -- and the library
;;;      never calls it, because what it produces still speaks (ADD ZZ-RING).
;;;   2. declare-instance! installs the per-slot macetes ZZ-RING@ADD :
;;;      (ADD ZZ-RING) -> binplus.
;;;   3. binplus-apply : binplus(x,y) == x + y.
;;;
;;; The LAST MILE -- 1 then 2 then 3 -- was nobody's job.  A transported theorem
;;; landed in the accessor language while every goal in the library speaks `+',
;;; so in practice nobody transported anything.  This file composes the three.
;;;
;;; It is IMPS's "transportable macete", in the one form VNB can honestly
;;; support today: a rewrite proved in a structure, carried to an instance along
;;; the instance's own slot equations.  (Carrying a macete along a VIEW -- S seen
;;; as S' by def-view-as -- is the next step, and wants the view's component maps
;;; to be rewrite rules in the same way.  Not done here.)
;;;
;;; NOTHING here is asserted.  transport! PROVES the surface form: it cites the
;;; generic theorem and rewrites with the instance's own definitional slot
;;; macetes.  The bill of the transported theorem is the bill of the generic one.

;;; -----------------------------------------------------------------------
;;; The surface bridges: the equations that take an instance's slot VALUES down
;;; to the operators a reader actually writes.  Numeric-domain specific by
;;; nature; a non-numeric instance (MAT-RING) simply has none fire.
(define *surface-bridge-theorems*
  '(binplus-apply bintimes-apply binneg-apply))

;;; A RULE is (schema-vars conditions source replacement) -- the same four things
;;; make-elementary-macete takes, kept as data so the SAME rule set can both
;;; rewrite a formula (to state the transported theorem) and drive a macete (to
;;; prove it).  One source of truth; the two cannot drift apart.
(define (tr--theorem-rule name)
  (let ((f (lookup-theorem name)))
    (if (not f)
        (error "transport: no such theorem (surface bridge)" name)
        (call-with-values
          (lambda () (strip-foralls (prenex-positive f)))
          (lambda (schema-vars core)
            (call-with-values
              (lambda () (extract-rewrite-patterns core))
              (lambda (conditions source replacement)
                (list schema-vars conditions source replacement))))))))

(define (instance-surface-rules instance)
  (map (lambda (n) (cons n (tr--theorem-rule n)))
       (instance-surface-macete-names instance)))

;;; -----------------------------------------------------------------------
;;; Apply ONE named rule to a formula, purely.  Returns the rewritten formula,
;;; or #f if it does not fire.  This is the single primitive both halves use:
;;; surface-normalize (to STATE the transported theorem) and tr--surface-
;;; assumption! (to have the KERNEL redo the same rewrite inside the proof).
;;; They cannot drift apart, because it is the same rule and the same rewriter.
(define (tr--rewrite-1 rule f)
  (let* ((r    (cdr rule))                   ; (schema-vars conditions source repl)
         (res  (rewrite-expr (caddr r) (cadddr r) (car r) (cadr r) f '()))
         (f*   (car res)))
    (and (not (alpha-equiv? f* f)) f*)))

;;; (surface-normalize INSTANCE formula) -- rewrite to the surface language.
;;; Pure: no proof, no node.  Used to STATE what transport! will then prove.
(define (surface-normalize instance formula)
  (let ((rules (instance-surface-rules instance)))
    (let loop ((f formula) (fuel 100))
      (if (= fuel 0)
          (error "surface-normalize: rules did not reach a fixpoint" instance)
          (let ((f* (fold-left (lambda (acc rule) (or (tr--rewrite-1 rule acc) acc))
                               f rules)))
            (if (alpha-equiv? f* f) f (loop f* (- fuel 1))))))))

;;; The NAMES of the rewrites, in the order they must fire: an instance's slot
;;; equations first ((ADD ZZ-RING) == binplus), then the surface bridges
;;; (binplus(x,y) == x + y).
;;;
;;; Each is a THEOREM, and that is the whole point.  The hypothesis side of the
;;; macete machinery (apply-macete-to-assumption!) rebuilds its rule from
;;; (lookup-theorem name), so it can only rewrite an assumption with a macete
;;; that is a theorem -- a compound macete cannot rewrite an assumption at all,
;;; and neither could the instance slot macetes until declare-instance! started
;;; installing them as theorems (structures.scm).  transport! rewrites a landed
;;; FACT, so it needs all of them nameable.
(define (instance-surface-macete-names instance)
  (let ((entry (hash-table-ref/default *structure-instances* instance #f)))
    (if (not entry)
        (error "transport: not a declared instance" instance)
        (append (map cadr (cdr entry))            ; ZZ-RING@CARR, ZZ-RING@ADD, ...
                *surface-bridge-theorems*))))

;;; Rewrite the cited ASSUMPTION to the surface language, to fixpoint.  Each step
;;; is the ordinary hypothesis-side macete rule (mac-h), so nothing new is
;;; trusted; we know in advance what each step must produce, so no context
;;; diffing and no guessing about what landed.
(define (tr--surface-assumption! instance hyp)
  (let ((rules (instance-surface-rules instance)))
    (let loop ((h hyp) (fuel 100))
      (if (= fuel 0)
          (error "transport!: assumption rewriting did not terminate" instance)
          (let scan ((rs rules) (cur h) (fired #f))
            (cond
              ((null? rs)
               (if fired (loop cur (- fuel 1)) cur))
              (else
               (let ((next (tr--rewrite-1 (car rs) cur)))
                 (if (not next)
                     (scan (cdr rs) cur fired)
                     (begin
                       (mac-h (car (car rs)) cur)      ; the kernel redoes it
                       (scan (cdr rs) next #t)))))))))))

;;; The same rewriting, on the GOAL.  `mac' has always been able to do this (the
;;; goal side only ever needed the macete procedure); what it lacked was a reason
;;; to iterate.  Used to prove IS-RING(ZZ-RING) -- unfold the definition, push
;;; the accessors down to the surface, and the conjuncts become the ordinary
;;; arithmetic axioms.
(define (surface-goal! instance)
  (let ((rules (instance-surface-rules instance)))
    (let loop ((fuel 100))
      (if (= fuel 0)
          (error "surface-goal!: did not reach a fixpoint" instance)
          (let* ((g     (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
                 (fired (let scan ((rs rules) (cur g) (any #f))
                          (cond
                            ((null? rs) any)
                            ((tr--rewrite-1 (car rs) cur)
                             => (lambda (next)
                                  (mac (car (car rs)))
                                  (scan (cdr rs) next #t)))
                            (else (scan (cdr rs) cur any))))))
            (if fired (loop (- fuel 1)) 'done))))))

;;; -----------------------------------------------------------------------
;;; (transport! GENERIC INSTANCE WITNESS [NAME]) -- prove and install the surface
;;; form of GENERIC at INSTANCE.
;;;
;;;   GENERIC   a theorem (FORALL s (IMPLIES (IS-X s) BODY))
;;;   INSTANCE  a declare-instance!'d constant, e.g. ZZ-RING
;;;   WITNESS   the theorem (IS-X INSTANCE), e.g. zz-is-ring
;;;
;;; e.g. (transport! 'group-cancel-right 'ZZ-RING 'zz-is-ring)
;;;      installs   forall a,b,c in ZZ. a + c = b + c => a = b
;;;      as         group-cancel-right@zz-ring
;;;
;;; The proof, in full: state the surface form; bring the IS-X witness into
;;; context; `fact' the generic theorem at the instance (which detaches the
;;; witness and lands BODY[s:=INSTANCE], in the accessor language); rewrite THAT
;;; assumption with the instance's surface macete; `ass'.  Kernel rules only.
(define (transport! generic instance witness #!optional name)
  (let* ((g (lookup-theorem generic)))
    (if (not g) (error "transport!: no such theorem" generic))
    (if (not (and (pair? g) (eq? (car g) 'FORALL)))
        (error "transport!: theorem is not (FORALL s (IMPLIES (IS-X s) ...))" generic))
    (let* ((svar (quantifier-var g))
           (body0 (quantifier-body g)))
      (if (not (and (pair? body0) (eq? (car body0) 'IMPLIES)))
          (error "transport!: theorem has no (IS-X s) guard" generic))
      (let* ((body     (binary-right body0))
             (inst-body (subst-free svar instance body))
             (surf     (surface-normalize instance inst-body))
             (new-name (if (default-object? name)
                           (symbol-append generic '@
                                          (string->symbol
                                            (string-downcase (symbol->string instance))))
                           name)))
        (if (alpha-equiv? surf inst-body)
            (error "transport!: nothing to normalize -- is INSTANCE declared?" instance))
        (sp (make-wff surf))
        (ta witness)                        ; (IS-X INSTANCE) into context
        (let ((landed (tr--deepest (lambda () (fact generic instance)))))
          (tr--surface-assumption! instance landed))   ; accessor -> surface
        (ass)
        (if (not (proof-done? *ps*))
            (begin
              (display "\n*** transport!: ") (display generic)
              (display " at ") (display instance) (display " did NOT close.\n")
              (for-each (lambda (l)
                          (display "   GOAL: ")
                          (display (expression->string
                                     (wff-formula (sequent-node-assertion l))))
                          (newline))
                        (proof-open-goals *ps*))
              (error "transport!: unfinished" generic instance)))
        (qed new-name)
        new-name))))

;;; `fact' lands its whole instantiation chain (the theorem, each partly-peeled
;;; form, the detached result).  The one we want is the deepest -- the landing no
;;; other landing contains.  (driver-kit has dk-deepest, but it loads later, and
;;; transport! is used BY structure files.)
(define (tr--deepest thunk)
  (let* ((asms0 (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
    (thunk)
    (let* ((asms1 (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
           (new   (let loop ((as asms1) (acc '()))
                    (cond ((null? as) (reverse acc))
                          ((member (car as) asms0) (loop (cdr as) acc))
                          (else (loop (cdr as) (cons (car as) acc)))))))
      (if (null? new)
          (error "transport!: `fact' landed nothing -- silent no-op")
          (or (find-first
                (lambda (a)
                  (not (find-first (lambda (b) (and (not (eq? a b)) (tr--contains? a b)))
                                   new)))
                new)
              (car new))))))

(define (tr--contains? form sub)
  (cond ((equal? form sub) #t)
        ((pair? form) (or (tr--contains? (car form) sub) (tr--contains? (cdr form) sub)))
        (else #f)))
