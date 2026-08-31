;;; discrete-space.scm -- THE FIRST WITNESS OF A MEASURABLE SPACE, and the
;;; first outright inhabitant of TOP-SPACE.
;;;
;;;     DISCRETE-SPACE(a)  ==  ( a,  POWER(a) )
;;;
;;; One tuple, two structures.  TOP-SPACE and MEASURABLE-SPACE have the SAME
;;; shape -- carrier PTS at slot 1, a `constant' slot typed into
;;; POWER(POWER(PTS)) at slot 2 (top-space.scm:38, measurable-space.scm:69) --
;;; so a single `def-functoid' serves both, and the accessor macetes for OPENS
;;; and SIGMA both reduce to (NTH 2 s).  Everything the two predicates then ask
;;; is a closure property of POWER(a), which is why the whole file is one
;;; lemma family about the power set and two three-line headlines.
;;;
;;; WHY.  `structure-exemplification-audit' (audit.scm:1145) put MEASURABLE-SPACE
;;; on its UNWITNESSED list -- nothing in the tree exhibited a measurable space
;;; at all -- and TOP-SPACE only on its REACHABLE list, inhabited by a
;;; construction (the metric topology) whose own hypothesis is a metric space.
;;; The discrete space is the cheapest witness either predicate can have: no
;;; separation, no metric, no countability, and a hypothesis (`a in SET') that
;;; is not a structure hypothesis at all, so it SEEDS rather than merely
;;; reaches.  A structure nothing instantiates has never had its satisfiability
;;; tested by anything, which is how IS-NORMED-VECTOR-SPACE pinned length(scal)
;;; to 6 and to 7 at once for months (rr-nvs-exemplification.scm).
;;;
;;; WHAT WAS MISSING, and it is the reason this file is mostly lemmas: the tree
;;; had NO theorem about POWER at all.  `power-set' and `power-set-membership'
;;; (theory.scm:297,300) are the only two statements naming it, and every
;;; consumer had to unfold the membership iff by hand.  The seven lemmas below
;;; are the closure facts any power-set argument wants -- sethood, the two
;;; directions of the membership iff, the whole set, the empty set, binary
;;; intersection, relative complement, arbitrary union, indexed countable union
;;; -- and each is `modulo 0'.  `subset-refl' goes in beside them: three files
;;; proved reflexivity inline, one of them with the comment "(no named
;;; subset-refl)" (nn-nested-subset-chain-proof.scm:42).
;;;
;;; NOTE ON THE COMPLEMENT LEMMA.  `power-complement-closed' is UNGUARDED in the
;;; set being complemented: COMPLEMENT-IN(a,b) is a subclass of a whatever b is,
;;; so the sigma-algebra's complement clause needs nothing about its argument
;;; beyond `a in SET'.  That is a fact about the relative complement, not an
;;; accident of the discrete case.
;;;
;;; Needs: subset-lemmas (subset-mem-fwd, subclass-of-set-is-set), top-space,
;;; measurable-space (and through it sigma-algebra), number-systems (nn-is-set).

;;; -----------------------------------------------------------------------
;;; file-local helpers (ds- prefix; driver-kit holds anything shared)
;;; -----------------------------------------------------------------------

;;; `sp' REPORTS a bad statement and returns -- it does not raise -- so the
;;; previous (completed) proof stays live and the next `qed' installs THAT proof
;;; under the new name.  Silent, sound, and a lie about what the name means:
;;; hit on the first run of this file, where a mis-shaped `forall-guarded' call
;;; installed power-mem-intro's statement as `power-whole-in'.  Every statement
;;; below goes through this instead.
(define (ds-sp! form)
  (sp (make-wff form))
  (if (not (alpha-equiv? (dk-goal) form))
      (error "ds-sp!: sp did not install this statement; a stale proof is live"
             form)))

(define (ds-goal-of s) (wff-formula (sequent-node-assertion s)))

;;; Peel the leading FORALL/IMPLIES prefix, guarding on PROGRESS -- `di' takes
;;; a prefix, not always the whole one, so a fixed count is a guess.
(define (ds-peel!)
  (let loop ((n 12))
    (let ((before (dk-goal)))
      (if (and (> n 0) (pair? before) (memq (car before) '(FORALL IMPLIES)))
          (begin (di)
                 (if (not (equal? (dk-goal) before)) (loop (- n 1))))))))

;;; Focus the FIRST open leaf whose goal satisfies PRED; error if there is none.
;;; A focus helper that returns #f and leaves focus put hides every later bug.
(define (ds-focus! pred)
  (let ((ls (filter (lambda (l) (pred (ds-goal-of l))) (proof-leaves))))
    (if (null? ls)
        (error "ds-focus!: no open leaf matching")
        (begin (dk-focus! (car ls)) (car ls)))))

(define (ds-disch pred thunk) (ds-focus! pred) (thunk))

;;; The SOFT variant, for a conjunct that may ALREADY BE CLOSED when the split
;;; reaches it.  `dg-post!' hash-conses sequent nodes by alpha-equivalence of
;;; the assertion plus equality of the context, so the sigma-algebra clause
;;; `a in SET' is the very node the outer shape conjunct `PTS(s) in SET' was
;;; closed at -- it comes back grounded and never becomes an open leaf.  Not an
;;; error, and not something to discover by watching a driver die.
(define (ds-disch? pred thunk)
  (if (pair? (filter (lambda (l) (pred (ds-goal-of l))) (proof-leaves)))
      (ds-disch pred thunk)))

;;; "the formula mentions the symbol H anywhere" -- the discriminator used for
;;; the law conjuncts, whose eigenvariable names are chosen by the rewriter
;;; (the structure's own binders can be renamed by capture-avoidance when the
;;; instance term is substituted in) and so cannot be written down in advance.
(define (ds-ment? h)
  (lambda (f)
    (let walk ((x f))
      (cond ((eq? x h) #t)
            ((pair? x) (or (walk (car x)) (walk (cdr x))))
            (else #f)))))

;;; The SUBJECT of the focus goal (IN subj class) -- eigenvariables are read off
;;; the GOAL, never off the context, whose order is not the peel order.
(define (ds-subject) (cadr (dk-goal)))

;;; "the goal is (HEAD arg ...) with (car arg) = SUB" -- discriminating on the
;;; SUBJECT, which is unique per conjunct, not on the head, which is shared.
(define (ds-subj? head sub)
  (lambda (g)
    (and (pair? g) (eq? (car g) head)
         (or (eq? (cadr g) sub)
             (and (pair? (cadr g)) (eq? (car (cadr g)) sub))))))

;;; Split every top-level AND among the open leaves, to exhaustion.
(define (ds-split-ands!)
  (let lp ()
    (let ((m (filter (lambda (l) (let ((g (ds-goal-of l)))
                                   (and (pair? g) (eq? (car g) 'AND))))
                     (proof-leaves))))
      (when (pair? m) (dk-focus! (car m)) (di) (lp)))))

;;; Run THUNK (which splits the focus goal) and hand each opened leaf to F.
(define (ds-each-opened thunk f)
  (for-each (lambda (l) (dk-focus! l) (f l)) (dk-opened thunk)))

;;; The unique landed assumption with head H, out of what THUNK landed.
(define (ds-landed-head thunk h)
  (dk-landed-find thunk (dk-head? h)))

;;; -----------------------------------------------------------------------
;;; subset-refl -- proved inline in three files; named here once.
;;; -----------------------------------------------------------------------

(ds-sp! '(FORALL a_ (SUBSET a_ a_)))
(di)
(mac 'subset-def)
(di)
(ass)
(qed 'subset-refl)
(topic! 'subset-refl 'plumbing)

;;; -----------------------------------------------------------------------
;;; The power-set lemma family.
;;; -----------------------------------------------------------------------

;;; (1) a member of a power set is a set.
(ds-sp! (forall-guarded '(a_ b_) '((IN b_ (POWER a_))) '(IN b_ SET)))
(ds-peel!)
(fact 'membership-implies-sethood 'b_ '(POWER a_))
(ass)
(qed 'power-mem-sethood)
(topic! 'power-mem-sethood 'set-quotient)

;;; (2) ELIM: a member of POWER(a) is included in a.  Antecedents CURRIED so
;;; `fact' can detach them one at a time against the live context.
(ds-sp! (forall-guarded '(a_ b_ z_)
                '((IN b_ (POWER a_)) (IN z_ b_))
                '(IN z_ a_)))
(ds-peel!)
(let* ((h (dk-landed-1 (lambda () (mac-h 'power-set-membership '(IN b_ (POWER a_))))))
       (parts (dk-split! h))
       (u (car (filter (dk-head? 'FORALL) parts))))
  (inst+ u 'z_))
(ass)
(qed 'power-mem-in)
(topic! 'power-mem-in 'set-quotient)

;;; (3) INTRO: a set included in a is a member of POWER(a).
(ds-sp! (forall-guarded '(a_ b_)
                '((IN b_ SET) (FORALL z_ (IMPLIES (IN z_ b_) (IN z_ a_))))
                '(IN b_ (POWER a_))))
(ds-peel!)
(mac 'power-set-membership)
(ds-each-opened (lambda () (di)) (lambda (l) (ass)))
(qed 'power-mem-intro)
(topic! 'power-mem-intro 'set-quotient)

;;; (4) the whole set is a member of its own power set.
(ds-sp! (forall-guarded '(a_) '((IN a_ SET)) '(IN a_ (POWER a_))))
(ds-peel!)
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL) (begin (di) (ass)) (ass))))
(qed 'power-whole-in)
(topic! 'power-whole-in 'set-quotient)

;;; (5) the empty set is a member of every power set.
(ds-sp! '(FORALL a_ (IN EMPTY-SET (POWER a_))))
(ds-peel!)
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL)
        (let* ((h (dk-landed-1 (lambda () (di))))
               (z (cadr h)))
          (fact 'empty-set-has-no-members z)
          (prop))
        (begin (fact 'empty-set-is-set) (ass)))))
(qed 'power-empty-in)
(topic! 'power-empty-in 'set-quotient)

;;; (6) closed under binary intersection.
(ds-sp! (forall-guarded '(a_ u_ v_)
                '((IN u_ (POWER a_)) (IN v_ (POWER a_)))
                '(IN (INTERSECTION u_ v_) (POWER a_))))
(ds-peel!)
(fact 'power-mem-sethood 'a_ 'u_)
(have! '(OR (IN u_ SET) (IN v_ SET)) (lambda () (oi-l) (ass)))
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL)
        (let* ((h (dk-landed-1 (lambda () (di))))
               (z (cadr h)))
          (dk-split! (dk-landed-1 (lambda () (mac-h 'intersection-membership h))))
          (fact 'power-mem-in 'a_ 'u_ z)
          (ass))
        (begin (fact 'intersection-set-closure 'u_ 'v_) (ass)))))
(qed 'power-inter-closed)
(topic! 'power-inter-closed 'set-quotient)

;;; (7) closed under relative complement -- UNGUARDED in the second argument.
(ds-sp! (forall-guarded '(a_ b_) '((IN a_ SET))
                '(IN (COMPLEMENT-IN a_ b_) (POWER a_))))
(ds-peel!)
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL)
        (let ((h (dk-landed-1 (lambda () (di)))))
          (dk-split! (dk-landed-1 (lambda () (mac-h 'complement-in-membership h))))
          (ass))
        (begin (fact 'complement-in-set-closure 'a_ 'b_) (ass)))))
(qed 'power-complement-closed)
(topic! 'power-complement-closed 'set-quotient)

;;; (8) closed under the union of an arbitrary SUBFAMILY -- the topology's
;;; arbitrary-union law.  The family is a set because it is a subclass of the
;;; set POWER(a) (subclass-of-set-is-set).
(ds-sp! (forall-guarded '(a_ fam_) '((IN a_ SET) (SUBSET fam_ (POWER a_)))
                '(IN (BIG-UNION u_ fam_ u_) (POWER a_))))
(ds-peel!)
(fact 'power-set 'a_)
(fact 'subclass-of-set-is-set 'fam_ '(POWER a_))
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL)
        (let* ((h (dk-landed-1 (lambda () (di))))
               (z (cadr h))
               (new (dk-landed (lambda () (bu-me h))))
               (mem (car (filter (lambda (f) (equal? (caddr f) 'fam_)) new)))
               (w   (cadr mem)))
          (fact 'subset-mem-fwd 'fam_ '(POWER a_) w)
          (fact 'power-mem-in 'a_ w z)
          (ass))
        (ds-each-opened (lambda () (bu-set))
          (lambda (l2)
            (if (eq? (car (dk-goal)) 'FORALL)
                (let* ((h2 (dk-landed-1 (lambda () (di))))
                       (e  (cadr h2)))
                  (fact 'membership-implies-sethood e 'fam_)
                  (ass))
                (ass)))))))
(qed 'power-big-union-closed)
(topic! 'power-big-union-closed 'set-quotient)

;;; (9) closed under the union of a COUNTABLE INDEXED family -- the
;;; sigma-algebra's countable-union law.
(ds-sp! (forall-guarded '(a_ f_) '((IN f_ (FUN NN (POWER a_))))
                '(IN (BIG-UNION n_ NN (f_ n_)) (POWER a_))))
(ds-peel!)
(define ds-fc
  (car (filter (dk-head? 'FORALL)
               (dk-split! (dk-landed-1
                 (lambda () (mac-h 'fun-codomain-iff '(IN f_ (FUN NN (POWER a_))))))))))
(mac 'power-set-membership)
(ds-each-opened (lambda () (di))
  (lambda (l)
    (if (eq? (car (dk-goal)) 'FORALL)
        (let* ((h (dk-landed-1 (lambda () (di))))
               (z (cadr h))
               (new (dk-landed (lambda () (bu-me h))))
               (mem (car (filter (lambda (f) (equal? (caddr f) 'NN)) new)))
               (w   (cadr mem)))
          (inst+ ds-fc w)
          (fact 'power-mem-in 'a_ (list 'f_ w) z)
          (ass))
        (ds-each-opened (lambda () (bu-set))
          (lambda (l2)
            (if (eq? (car (dk-goal)) 'FORALL)
                (let* ((h2 (dk-landed-1 (lambda () (di))))
                       (e  (cadr h2)))
                  (inst+ ds-fc e)
                  (fact 'power-mem-sethood 'a_ (list 'f_ e))
                  (ass))
                (begin (fact 'nn-is-set) (ass))))))))
(qed 'power-fun-union-closed)
(topic! 'power-fun-union-closed 'set-quotient)

;;; -----------------------------------------------------------------------
;;; The structure, and its two slot read-offs.
;;;
;;; PROVEN, not asserted: `def-structure' mints a `definitional' accessor macete
;;; (ACC s) -> (NTH k s) and `nth-r' projects a literal LIST, so the read-off is
;;; three definitional rewrites and a kernel projection.  Stated with QUASI-
;;; equality and closed with `qrfl': `=' is partial, so `t = t' is a definedness
;;; claim, and the definedness of a power set is not something a slot read-off
;;; should have to establish (fin-subset-monoid.scm sets this out).
;;; The accessor is reduced with `slot', never `mac' -- test-suite.scm's
;;; accessor-callsite-audit fails any file that fires an accessor macete by name.
;;; -----------------------------------------------------------------------

(def-functoid 'DISCRETE-SPACE '(a_)
  '(LIST a_ (POWER a_)))
(notation! 'DISCRETE-SPACE 'kind 'functoid 'arity 1
           'english "the discrete space on $1")

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (== (PTS (DISCRETE-SPACE a_)) a_))))
  (ds-peel!) (slot 'pts) (mac 'discrete-space) (nth-r) (qrfl)))
(qed 'ds-pts)
(topic! 'ds-pts 'plumbing)

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (== (OPENS (DISCRETE-SPACE a_)) (POWER a_)))))
  (ds-peel!) (slot 'opens) (mac 'discrete-space) (nth-r) (qrfl)))
(qed 'ds-opens)
(topic! 'ds-opens 'plumbing)

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (== (SIGMA (DISCRETE-SPACE a_)) (POWER a_)))))
  (ds-peel!) (slot 'sigma) (mac 'discrete-space) (nth-r) (qrfl)))
(qed 'ds-sigma)
(topic! 'ds-sigma 'plumbing)

;;; -----------------------------------------------------------------------
;;; HEADLINE 1: the discrete space is a topological space.
;;; -----------------------------------------------------------------------

(ds-sp! (forall-guarded '(a_) '((IN a_ SET))
                '(IS-TOP-SPACE (DISCRETE-SPACE a_))))
(ds-peel!)
(mac 'IS-TOP-SPACE)
;; rewrite both accessors ONCE, on the whole conjunction, before splitting
(mac 'ds-pts)
(mac 'ds-opens)
(ds-split-ands!)

;; length(DISCRETE-SPACE(a)) = 2
(ds-disch (ds-subj? '= 'LENGTH)
  (lambda () (mac 'discrete-space) (len-r) (rfl)))

;; a in SET
(ds-disch (lambda (g) (equal? g '(IN a_ SET)))
  (lambda () (ass)))

;; POWER(a) in POWER(POWER(a))
(ds-disch (lambda (g) (equal? g '(IN (POWER a_) (POWER (POWER a_)))))
  (lambda () (fact 'power-set 'a_) (fact 'power-whole-in '(POWER a_)) (ass)))

;; {} is open
(ds-disch (lambda (g) (equal? g '(IN EMPTY-SET (POWER a_))))
  (lambda () (fact 'power-empty-in 'a_) (ass)))

;; a is open
(ds-disch (lambda (g) (equal? g '(IN a_ (POWER a_))))
  (lambda () (fact 'power-whole-in 'a_) (ass)))

;; closed under binary intersection
(ds-disch (ds-ment? 'INTERSECTION)
  (lambda ()
    (ds-peel!)
    (let ((t (ds-subject)))                  ; (INTERSECTION u v)
      (fact 'power-inter-closed 'a_ (cadr t) (caddr t)))
    (ass)))

;; closed under arbitrary union
(ds-disch (ds-ment? 'BIG-UNION)
  (lambda ()
    (ds-peel!)
    (let ((t (ds-subject)))                  ; (BIG-UNION u fam u)
      (fact 'power-big-union-closed 'a_ (caddr t)))
    (ass)))

(qed 'discrete-space-is-top-space)
(topic! 'discrete-space-is-top-space 'topology)

;;; -----------------------------------------------------------------------
;;; HEADLINE 2: the discrete space is a measurable space -- POWER(a) is the
;;; largest sigma-algebra on a.
;;; -----------------------------------------------------------------------

(ds-sp! (forall-guarded '(a_) '((IN a_ SET))
                '(IS-MEASURABLE-SPACE (DISCRETE-SPACE a_))))
(ds-peel!)
(mac 'IS-MEASURABLE-SPACE)
(mac 'ds-pts)
(mac 'ds-sigma)
(ds-split-ands!)

(ds-disch (ds-subj? '= 'LENGTH)
  (lambda () (mac 'discrete-space) (len-r) (rfl)))

(ds-disch (lambda (g) (equal? g '(IN a_ SET)))
  (lambda () (ass)))

(ds-disch (lambda (g) (equal? g '(IN (POWER a_) (POWER (POWER a_)))))
  (lambda () (fact 'power-set 'a_) (fact 'power-whole-in '(POWER a_)) (ass)))

;; IS-SIGMA-ALGEBRA(a, POWER(a)) -- unfold and take the five clauses
(ds-disch (dk-head? 'IS-SIGMA-ALGEBRA)
  (lambda ()
    (mac 'IS-SIGMA-ALGEBRA)
    (ds-split-ands!)

    ;; already closed: the same sequent as the shape conjunct above
    (ds-disch? (lambda (g) (equal? g '(IN a_ SET)))
      (lambda () (ass)))

    (ds-disch (dk-head? 'SUBSET)
      (lambda () (fact 'subset-refl '(POWER a_)) (ass)))

    (ds-disch (lambda (g) (equal? g '(IN a_ (POWER a_))))
      (lambda () (fact 'power-whole-in 'a_) (ass)))

    ;; complements
    (ds-disch (ds-ment? 'COMPLEMENT-IN)
      (lambda ()
        (ds-peel!)
        (let ((t (ds-subject)))              ; (COMPLEMENT-IN a b)
          (fact 'power-complement-closed 'a_ (caddr t)))
        (ass)))

    ;; countable unions
    (ds-disch (ds-ment? 'BIG-UNION)
      (lambda ()
        (ds-peel!)
        (let ((t (ds-subject)))              ; (BIG-UNION n NN (f n))
          (fact 'power-fun-union-closed 'a_ (car (cadddr t))))
        (ass)))))

(qed 'discrete-space-is-measurable-space)
(topic! 'discrete-space-is-measurable-space 'set-quotient)
