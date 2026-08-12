;;; subtype-laws.scm -- the trivial subtype-subsumption laws, PROVEN.
;;;
;;; These four facts ("every X is a Y") were long asserted as bare axioms,
;;; not because they are deep but because, pre-`mac-h`, the IS-X / membership
;;; hypothesis could not be unfolded -- so the subsumption had to be taken on
;;; faith.  With `mac-h` (the hypothesis-side unfold) each is a one-breath
;;; proof, modulo 0 (trusted base only).  A VISA audit (asserted leaves vs.
;;; the PSS) flagged them as phantom debt; this file retires them.
;;;
;;; Loaded AFTER interactive (sp/di/mac-h/qed) and proof-debt (so qed can
;;; bill the proof).  The four proofs are trivial -- they add negligible
;;; load time and are NOT guarded by VNB_SKIP_PROOFS, so the names are always
;;; installed (as proven), here in place of the axioms removed from
;;; abelian-group.scm / commutative-ring.scm / euclidean-ring.scm /
;;; injection.scm.
;;;
;;; See memory project_subtype_laws_retired / project_prop_3_14_proven for the
;;; forward-reasoning helpers this reuses.

;;; --- local proof helpers (prefixed to avoid clobbering globals) ---------
(define (stl--leaves)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (stl--any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (stl--goalof s) (wff-formula (sequent-node-assertion s)))
(define (stl--hyp-sub substr)
  (let ((w (stl--any (lambda (w) (string-search-forward substr (expression->string (wff-formula w)) 0))
                     (sequent-node-assumptions (proof-state-focus *ps*)))))
    (and w (wff-formula w))))
(define (stl--split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (proof-state-focus *ps*))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))
;; Unified closer: ass any leaf whose goal is an assumption; else di an AND
;; goal; else mac-unfold a folded (head ...) goal.  Fuel-bounded.
(define (stl--close! head)
  (let loop ((fuel 400))
    (when (> fuel 0)
      (let ((asl (stl--any (lambda (s) (stl--any (lambda (w) (alpha-equiv? (wff-formula w) (stl--goalof s)))
                                                 (sequent-node-assumptions s)))
                           (stl--leaves))))
        (cond
          (asl (set-proof-state-focus! *ps* asl) (ass) (loop (- fuel 1)))
          (else
           (let ((andl (stl--any (lambda (s) (let ((g (stl--goalof s))) (and (pair? g) (eq? (car g) 'AND))))
                                 (stl--leaves))))
             (cond
               (andl (set-proof-state-focus! *ps* andl) (di) (loop (- fuel 1)))
               (else
                (let ((macl (stl--any (lambda (s) (let ((g (stl--goalof s))) (and (pair? g) (eq? (car g) head))))
                                      (stl--leaves))))
                  (when macl (set-proof-state-focus! *ps* macl) (mac head) (loop (- fuel 1)))))))))))))

;; Predicate subtype: FORALL s. IS-X(s) => IS-Y(s).
(define (stl--prove-pred! name isx isy hyp-unfold hypkey)
  (sp (make-wff (list 'FORALL 's (list 'IMPLIES (list isx 's) (list isy 's)))))
  (di) (di)
  (mac-h hyp-unfold (stl--hyp-sub hypkey))
  (stl--split-ands!)
  (stl--close! isy)
  (if (proof-done? *ps*)
      (qed name)
      (error "subtype-laws: failed to prove" name)))

;;; --- the four laws ------------------------------------------------------

;; Three predicate subtypes.  IS-ABELIAN-GROUP is a def-structure shape
;; predicate (unfold via its own name; goal IS-GROUP unfolds to a conjunct
;; subset).  The restrictive structures are IFF-defined (unfold the hyp via
;; is-X-def; the supertype is a literal RHS conjunct, closed by ass).
(stl--prove-pred! 'abelian-group-is-group
                  'IS-ABELIAN-GROUP 'IS-GROUP 'IS-ABELIAN-GROUP "abelian-group")
(stl--prove-pred! 'commutative-ring-is-ring
                  'IS-COMMUTATIVE-RING 'IS-RING 'is-commutative-ring-def "commutative-ring")
(stl--prove-pred! 'integral-domain-is-commutative-ring
                  'IS-INTEGRAL-DOMAIN 'IS-COMMUTATIVE-RING 'is-integral-domain-def "integral-domain")
(stl--prove-pred! 'euclidean-ring-is-integral-domain
                  'IS-EUCLIDEAN-RING 'IS-INTEGRAL-DOMAIN 'is-euclidean-ring-def "euclidean-ring")

;; COMM-MONOID is a def-structure shape with MONOID's accessors plus
;; is-commutative, so it is the abelian-group-is-group case exactly: unfold via
;; its own name, and IS-MONOID unfolds to a conjunct subset.  Asserted in
;; monoid.scm and unwarranted until 2026-08-10.  NOTE it moves no bill by
;; itself: the one bill it appears in (poly-is-ring) also names
;; nn-add-monoid-is-comm-monoid, which shadows it.
(stl--prove-pred! 'comm-monoid-is-monoid
                  'IS-COMM-MONOID 'IS-MONOID 'IS-COMM-MONOID "comm-monoid")

;; Membership subsumption: phi in BIJECTION(X,Y) => phi in INJECTION(X,Y).
;; Unfold both class memberships via their -membership-iff axioms; the FUN +
;; injective conjuncts coincide.
(sp (make-wff '(FORALL X (FORALL Y (FORALL phi
                 (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (INJECTION X Y))))))))
(di) (di) (di) (di)
(mac-h 'bijection-membership-iff (stl--hyp-sub "bijection"))
(stl--split-ands!)
(mac 'injection-membership-iff)
(stl--close! 'IN)                        ; goal already unfolded; just di + ass
(if (proof-done? *ps*)
    (qed 'bijection-is-injection)
    (error "subtype-laws: failed to prove bijection-is-injection"))

;; abelian-group-opr-comm: OPR commutes -- the is-commutative property projected
;; out of IS-ABELIAN-GROUP (the metric-sym shape: unfold IS-X, split, unfold the
;; property, ass).  Proven modulo 0; formerly asserted with a proof-warrant.
(sp (make-wff '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
   (FORALL a (IMPLIES (IN a (CARR s))
     (FORALL b (IMPLIES (IN b (CARR s))
       (= ((OPR s) a b) ((OPR s) b a))))))))))
(di) (di)
(mac-h 'IS-ABELIAN-GROUP (stl--hyp-sub "is-abelian-group"))
(stl--split-ands!)
(mac-h 'is-commutative (stl--hyp-sub "is-commutative"))
(ass)
(if (proof-done? *ps*) (qed 'abelian-group-opr-comm)
    (error "subtype-laws: failed to prove abelian-group-opr-comm"))

;;; --- the GROUP shape projections ----------------------------------------
;;;
;;; group-assoc / group-left-id / group-left-inv / group-identity-in were
;;; `theory-add-axiom!' in group.scm, unwarranted -- so every proof that used a
;;; group law billed `trust: none', the weakest report there is, for facts that
;;; are literally conjuncts of the IS-GROUP definition.  (ag-cancel-right's whole
;;; bill was these three.)  The alternative was to stamp them `definitional', as
;;; module.scm does with its projections; proving them is the same work and says
;;; something stronger, since the unfold is then CHECKED rather than asserted to
;;; exist.  Same shape as abelian-group-opr-comm above.
;;;
;;; Two cases.  A law that IS a whole operation-property (assoc) closes by `ass'
;;; the moment the property is unfolded -- the unfolding is the goal up to alpha.
;;; A law that is ONE SIDE of a two-sided property (left-id out of is-identity,
;;; left-inv out of has-inverses) needs the element binder peeled first, the
;;; unfolded property instantiated at the eigenvariable, its typing guard
;;; detached, and the conjunction split.  `stl--project!' does both: pass #f for
;;; SIDED? in the first case.  Every landed formula is taken by DIFF (dk-landed-1),
;;; never named by shape -- the eigenvariable is whatever `di' chose.

(define (stl--project! name goal propname propkey sided?)
  (sp (make-wff goal))
  (di) (di)
  (mac-h 'IS-GROUP (stl--hyp-sub "is-group"))
  (stl--split-ands!)
  (let ((unfolded (dk-landed-1 (lambda () (mac-h propname (stl--hyp-sub propkey))))))
    (if sided?
        (let* ((typing (dk-landed-1 (lambda () (di))))       ; (IN a (CARR s))
               (elt    (cadr typing))
               (inst-d (dk-landed-1 (lambda () (inst unfolded elt))))
               (both   (dk-landed-1 (lambda () (detach! inst-d)))))
          (dk-split! both))))
  (ass)
  (if (proof-done? *ps*)
      (qed name)
      (error "subtype-laws: failed to prove" name)))

(stl--project! 'group-assoc
  '(FORALL s (IMPLIES (IS-GROUP s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (FORALL c (IMPLIES (IN c (CARR s))
           (= ((OPR s) ((OPR s) a b) c)
              ((OPR s) a ((OPR s) b c)))))))))))
  'is-associative "is-associative" #f)

(stl--project! 'group-left-id
  '(FORALL s (IMPLIES (IS-GROUP s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (= ((OPR s) (IDEN s) a) a)))))
  'is-identity "is-identity" #t)

(stl--project! 'group-left-inv
  '(FORALL s (IMPLIES (IS-GROUP s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (= ((OPR s) ((INV s) a) a) (IDEN s))))))
  'has-inverses "has-inverses" #t)

;; group-identity-in: the `constant IDEN CARR' slot's own membership conjunct.
;; No property to unfold -- splitting the IS-GROUP conjunction puts it in the
;; context verbatim.
(sp (make-wff '(FORALL s (IMPLIES (IS-GROUP s) (IN (IDEN s) (CARR s))))))
(di) (di)
(mac-h 'IS-GROUP (stl--hyp-sub "is-group"))
(stl--split-ands!)
(ass)
(if (proof-done? *ps*) (qed 'group-identity-in)
    (error "subtype-laws: failed to prove group-identity-in"))
