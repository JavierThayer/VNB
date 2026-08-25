;;; fin-subset-monoid.scm -- FIN-SUBSETS(a) is a commutative monoid under union.
;;;
;;;     FIN-SUBSET-MONOID(a)  ==  ( FIN-SUBSETS(a),  union,  {} )
;;;
;;; and the headline
;;;
;;;     fin-subset-monoid-is-comm-monoid:
;;;         a in SET  =>  IS-COMM-MONOID(FIN-SUBSET-MONOID(a))
;;;
;;; This is the first of the two intended instances of the normed commutative
;;; monoid (the other being tuples under concatenation).  Its norm is CARD,
;;; which is SUBadditive and not additive, because union is idempotent.
;;;
;;; -----------------------------------------------------------------------
;;; WHY A FUNCTOID AND NOT `declare-instance!'.
;;;
;;; `declare-instance!' (structures.scm:377) mints a CONSTANT via `def-constant',
;;; so it cannot carry a parameter; the monoid of finite subsets is a family
;;; indexed by `a'.  The tree's pattern for a parametric structure is MAT-RING
;;; (structure-library/matrix.scm:296): a `def-functoid' whose body is the LIST
;;; of slots, plus a theorem `IS-X(F(params))' under the parameters' guards.
;;; theorem-library/mat-ring-proof.scm:94 is the worked example this file
;;; follows.
;;;
;;; -----------------------------------------------------------------------
;;; THE SLOT READ-OFFS ARE PROVEN HERE, NOT ASSERTED -- and that is a
;;; deliberate departure from the MAT-RING precedent.
;;;
;;; MAT-RING's six slot equations are `support' + `warrant! ... 'reference'
;;; (matrix.scm:707-720, "slot 1 of the MAT-RING tuple"), i.e. asserted debt for
;;; a fact that is pure bookkeeping.  They do not have to be.  `def-structure'
;;; mints, for each accessor, a `definitional' macete `(ACC s) -> (NTH k s)'
;;; (`install-accessor-macete!', structures.scm:287), and `nth-r'
;;; (`pi-nth-reduce!') projects a literal LIST structurally.  So
;;;
;;;     (slot 'carr) (mac 'fin-subset-monoid) (nth-r) (qrfl)
;;;
;;; proves the slot equation outright, `modulo 0' -- three definitional rewrites
;;; and a kernel projection.  All three read-offs below are theorems.
;;;
;;; They are stated with QUASI-equality `==' and closed with `qrfl', not with
;;; `=' and `rfl', and that is forced rather than stylistic: `=' is PARTIAL, so
;;; `t = t' is a definedness claim, and `pi-reflexivity!' duly refused
;;; `fin-subsets(a_) = fin-subsets(a_)' -- the definedness of the carrier is
;;; not something the slot read-off should have to establish.  `declare-instance!'
;;; mints its own slot equations with `==' for exactly this reason
;;; (structures.scm:404).  The EMPTY-SET slot was the one that proved under `='
;;; on the first attempt, because a constant denotes; that is what made the
;;; other two look like driver bugs rather than a partial-equality question.
;;;
;;; The accessor is reduced with `slot', NOT with `mac'.  That is enforced:
;;; test-suite.scm:3169 ("no file fires an accessor macete by name (use `slot')")
;;; runs `accessor-callsite-audit' over every file in the tree and fails if any
;;; of them writes `(mac 'carr)'.  The pin exists because the accessor reduction
;;; is currently GLOBAL and unconditional, and route 2 -- making it conditional
;;; on IS-X(s), which numbered carriers CARR1..CARRn will want -- stays cheap
;;; only while `slot' is the single procedure depending on it firing without a
;;; typing hypothesis (test-suite.scm:3161-3168).  Here `slot' does exactly what
;;; `mac' would: its instance/functor projection lookup finds nothing for a
;;; `def-functoid' argument, so it falls through to the plain accessor macete
;;; (interactive.scm:869-871).  Same rewrite, through the door that is counted.
;;; This cost a suite run to discover -- 899/1 -- which is the pin working.
;;;
;;; Retrofitting the same four lines onto MAT-RING's six would retire six
;;; `reference' assertions; it is not done here because it touches a file this
;;; task does not own.
;;;
;;; -----------------------------------------------------------------------
;;; THE BILLS.
;;;
;;;   fsm-carr / fsm-opr / fsm-iden          modulo 0
;;;   fin-subset-monoid-is-comm-monoid       modulo {card-subset-nn}
;;;                                            [trust: well-known]
;;;
;;; The single leaf arrives through fin-subsets-union-closed -> card-union-nn ->
;;; card-subset-nn, i.e. through "the union of two finite sets is finite", which
;;; is the one genuinely cardinal-theoretic fact the monoid needs.  Everything
;;; else -- associativity, commutativity, the identity, the typing of the
;;; operation -- is `modulo 0'.
;;;
;;; Needs: theorem-library/fin-subsets (the membership law and the four
;;; set-algebra lemmas), theorem-library/makeset-card-bound (union-comm),
;;; structure-library/monoid (COMM-MONOID), structure-library/operation-properties.

;;; --- file-local helpers (fm- prefix) ------------------------------------

(define (fm-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(forall implies)))
          (begin (di) (loop))))))

(define (fm-goal-of l) (wff-formula (sequent-node-assertion l)))

;; The leaves of the current proof.
(define (fm-leaves) (proof-leaves))

;; Focus the unique open leaf satisfying PRED, and error if there is none --
;; a focus helper that returns #f and leaves focus put hides every later bug
;; (CLAUDE.md).
(define (fm-focus! pred)
  (let ((ls (filter (lambda (l) (pred (fm-goal-of l))) (fm-leaves))))
    (if (null? ls)
        (error "fm-focus!: no leaf matching")
        (begin (dk-focus! (car ls)) (car ls)))))

;; "the goal is (HEAD (ACC ...) ...)" -- discriminating on the ACCESSOR, which
;; is unique per conjunct, rather than on the goal's head, which is shared.
(define (fm-is? head acc)
  (lambda (g)
    (and (pair? g) (eq? (car g) head)
         (pair? (cadr g)) (eq? (car (cadr g)) acc))))

(define (fm-disch pred thunk) (fm-focus! pred) (thunk))

;; Split every top-level AND among the open leaves, to exhaustion.
(define (fm-split-ands!)
  (let lp ()
    (let ((m (filter (lambda (l) (let ((g (fm-goal-of l)))
                                   (and (pair? g) (eq? (car g) 'and))))
                     (fm-leaves))))
      (when (pair? m)
        (dk-focus! (car m)) (di) (lp)))))

;; Rewrite the carrier and operation accessors away in the focus goal.  The
;; three read-offs are applied SITE BY SITE rather than as a block: a `mac' that
;; does not fire only warns, and a driver that lets a non-firing rewrite pass is
;; the silent no-op CLAUDE.md warns about.
(define (fm-co!) (mac 'fsm-carr) (mac 'fsm-opr))

;; Run THUNK on the focus leaf and return the leaves it opened BENEATH it.
;; Every conjunct below is scoped this way: the sibling conjuncts of the
;; IS-COMM-MONOID split are open at the same time, so a `for-each' over
;; `(proof-leaves)' would walk into a conjunct another block owns.
(define (fm-scoped thunk)
  (let* ((focus  (proof-state-focus *ps*))
         (before (filter (lambda (l) (not (eq? l focus))) (fm-leaves))))
    (thunk)
    (filter (lambda (l) (not (memq l before))) (fm-leaves))))

;; Beta-reduce the focus goal to exhaustion.  One `lam-b' takes one redex and
;; the associativity conjunct has four, so this loops -- but it tests for a
;; redex FIRST rather than firing and comparing, because a `lam-b' with nothing
;; to do warns, and a driver that prints warnings on its clean path trains the
;; reader to ignore them.
(define (fm-any p l) (and (pair? l) (or (p (car l)) (fm-any p (cdr l)))))
(define (fm-redex? e)
  (and (pair? e)
       (or (and (pair? (car e)) (eq? (car (car e)) 'vnb-lambda))
           (fm-any fm-redex? e))))
(define (fm-beta!)
  (let loop ((guard 0))
    (if (and (< guard 12) (fm-redex? (dk-goal)))
        (begin (lam-b) (loop (+ guard 1))))))

;;; -----------------------------------------------------------------------
;;; The structure.
;;;
;;; Slots, in COMM-MONOID's declared order (structure-library/monoid.scm:54):
;;; CARR, OPR, IDEN.  The operation is a two-binder VNB-LAMBDA over the
;;; CARTESIAN square of the carrier, which is what the `(op OPR (CARTESIAN CARR
;;; CARR) CARR)' clause types it into; `pi-lambda-type!' requires the declared
;;; domain to be LITERALLY the FUN's domain (primitive-inferences.scm:1386), so
;;; it is written out rather than abbreviated.

(def-functoid 'FIN-SUBSET-MONOID '(a_)
  '(LIST (FIN-SUBSETS a_)
         (VNB-LAMBDA (LIST x_ y_)
                     (CARTESIAN (FIN-SUBSETS a_) (FIN-SUBSETS a_))
                     (UNION x_ y_))
         EMPTY-SET))
(notation! 'FIN-SUBSET-MONOID 'kind 'functoid 'arity 1
           'english "the monoid of finite subsets of $1 under union")

;;; -----------------------------------------------------------------------
;;; The three slot read-offs, PROVEN.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (== (CARR (FIN-SUBSET-MONOID a_)) (FIN-SUBSETS a_)))))
  (fm-peel!) (slot 'carr) (mac 'fin-subset-monoid) (nth-r) (qrfl)))
(qed 'fsm-carr)
(topic! 'fsm-carr 'plumbing)

(quietly (lambda ()
  (sp (make-wff '(FORALL a_
        (== (OPR (FIN-SUBSET-MONOID a_))
            (VNB-LAMBDA (LIST x_ y_)
                        (CARTESIAN (FIN-SUBSETS a_) (FIN-SUBSETS a_))
                        (UNION x_ y_))))))
  (fm-peel!) (slot 'opr) (mac 'fin-subset-monoid) (nth-r) (qrfl)))
(qed 'fsm-opr)
(topic! 'fsm-opr 'plumbing)

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (== (IDEN (FIN-SUBSET-MONOID a_)) EMPTY-SET))))
  (fm-peel!) (slot 'iden) (mac 'fin-subset-monoid) (nth-r) (qrfl)))
(qed 'fsm-iden)
(topic! 'fsm-iden 'plumbing)

;;; -----------------------------------------------------------------------
;;; The headline.

(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET)
                 (IS-COMM-MONOID (FIN-SUBSET-MONOID a_))))))
(fm-peel!)
;; the two facts every conjunct below leans on, landed once
(fact 'fin-subsets-is-set 'a_)
(fact 'fin-subsets-has-empty 'a_)
(mac 'IS-COMM-MONOID)
(fm-split-ands!)

;; ---- 1. length(FIN-SUBSET-MONOID(a)) = 3 ----
(fm-disch (fm-is? '= 'length)
  (lambda () (mac 'fin-subset-monoid) (len-r) (rfl)))

;; ---- 2. carr in SET ----
(fm-disch (fm-is? 'in 'carr)
  (lambda () (mac 'fsm-carr) (ass)))

;; ---- 3. opr in FUN(CARTESIAN carr carr, carr) ----
;; `lam-t' opens TWO leaves -- the pointwise typing of the body and the SETHOOD
;; of the domain (CLAUDE.md) -- and BOTH are handled here by hand.  `dk-lam-t!'
;; is the usual shortcut but it cannot be used: its `dk-set-close!'
;; (driver-kit.scm:864) knows NN/RR/ZZ/QQ/CC, INTERVAL and CARTESIAN, and falls
;; through to `#f' on any other class, so on CARTESIAN(FIN-SUBSETS a,
;; FIN-SUBSETS a) it recurses into two halves it cannot close, then `ass'es a
;; goal that is not in the context.
;;
;; The binders are read OFF THE GOAL, never assumed: `pi--lambda-type-subgoal'
;; renames them apart, so the typing leaf quantifies `x__1242'/`y__1243', not
;; the `x_'/`y_' written in the lambda.
(fm-disch (fm-is? 'in 'opr)
  (lambda ()
    (fm-co!)
    (for-each
      (lambda (l)
        (dk-focus! l)
        (let ((g (dk-goal)))
          (if (and (pair? g) (eq? (car g) 'in) (eq? (caddr g) 'set))
              ;; sethood of the CARTESIAN domain
              (begin (mac 'cartesian-set-iff)
                     (for-each (lambda (k) (dk-focus! k) (ass))
                               (dk-opened (lambda () (di)))))
              ;; pointwise typing of the body
              (begin (fm-peel!)
                     (let ((t (cadr (dk-goal))))     ; (union x y)
                       (fact 'fin-subsets-union-closed 'a_ (cadr t) (caddr t)))
                     (ass)))))
      (fm-scoped (lambda () (lam-t))))))

;; ---- 4. iden in carr ----
(fm-disch (fm-is? 'in 'iden)
  (lambda () (mac 'fsm-carr) (mac 'fsm-iden) (ass)))

;; ---- 5. is-associative ----
;; The typing of the compound arguments goes ABOVE the beta, not below it: a
;; `lam-b' at an untyped argument still fires but OWES (IN arg domain) as an
;; extra leaf (CLAUDE.md, and mr-close-conj is the worked example).  So the two
;; `fin-subsets-union-closed' citations come first and `fm-beta!' second.
(fm-disch (lambda (g) (and (pair? g) (eq? (car g) 'is-associative)))
  (lambda ()
    (mac 'is-associative)
    (fm-co!)
    (fm-peel!)
    ;; goal is (= (OP (OP u v) w) (OP u (OP v w))) with OP the lambda; read the
    ;; three eigenvariables off its LEFT side rather than trusting the names
    ;; the def-predicate happens to use.
    (let* ((lhs (cadr (dk-goal)))          ; (LAM (LAM u v) w)
           (inner (cadr lhs))              ; (LAM u v)
           (u (cadr inner)) (v (caddr inner)) (w (caddr lhs)))
      (fact 'fin-subsets-union-closed 'a_ u v)
      (fact 'fin-subsets-union-closed 'a_ v w)
      (fm-beta!)
      (fact 'union-assoc u v w)
      (ass))))

;; ---- 6. is-identity ----
;; The conjunct is an AND of the two sides, so it opens two leaves and each is
;; scoped to this conjunct -- iterating over ALL open leaves here would walk
;; into the is-commutative conjunct, which is still open.
;; union-empty-right gives the RIGHT identity outright; the LEFT one is
;; union-comm composed with it.
(fm-disch (lambda (g) (and (pair? g) (eq? (car g) 'is-identity)))
  (lambda ()
    (mac 'is-identity)
    (fm-co!) (mac 'fsm-iden)
    (fm-peel!)
    (for-each
      (lambda (l)
        (dk-focus! l)
        (fm-beta!)
        (let* ((g (dk-goal)) (u (caddr g)))   ; (= (UNION .. ..) u)
          (fact 'union-empty-right u)
          (if (eq? (cadr (cadr g)) 'empty-set)
              (begin (fact 'union-comm 'EMPTY-SET u)
                     (subst (list '= (list 'UNION 'EMPTY-SET u)
                                     (list 'UNION u 'EMPTY-SET)))))
          (ass)))
      (fm-scoped (lambda () (di))))))

;; ---- 7. is-commutative ----
(fm-disch (lambda (g) (and (pair? g) (eq? (car g) 'is-commutative)))
  (lambda ()
    (mac 'is-commutative)
    (fm-co!)
    (fm-peel!)
    (let* ((lhs (cadr (dk-goal))) (u (cadr lhs)) (v (caddr lhs)))
      (fm-beta!)
      (fact 'union-comm u v)
      (ass))))

(qed 'fin-subset-monoid-is-comm-monoid)
(topic! 'fin-subset-monoid-is-comm-monoid 'algebra)
