;;; strand-messages-laws.scm -- THE MESSAGES OF STRAND SPACES (the user's model): their laws.
;;; (~/notes/notes-60.txt item (a); the definitions are structure-library/strand-messages.scm.)
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06.  This file REPLACES, in place, S-1's
;;; laws of the paper's algebra (archive/2026-10-06/strand-messages-laws.scm, 56 theorems on
;;; ATOM / CAT / ENC); the method is S-1's, the shapes are the user's: a token, or an n-ary list
;;; of messages.  Helper prefix: sml-.
;;;
;;; Every theorem below bills `modulo 0'.  The oracles that appear on some of them are `arith'
;;; (ground numeral facts) and `ineq' (NN linear arithmetic through dk-nn!, for the rank).
;;; Nothing is asserted, stamped or warranted.  T is the token set; A is MSG-SET(T); "message"
;;; means a member of A, "list of messages" a member of TUPLES(A).
;;;
;;; WHAT IS PROVEN (in this order)
;;;  1. pair-self-member, pair-self-eq            a set is the one member of PAIR(a, a)  [kept]
;;;  2. msg-stage-token, -keep, -list             the stage clauses, introduction
;;;     msg-stage-zero-elim, msg-stage-succ-cases ... and elimination
;;;     msg-stage-add                             S_j is included in S_(j + d)            [kept]
;;;  3. msg-set-unfold, msg-set-intro, msg-set-elim   A is the union of the stages         [kept]
;;;     token-in-msgs                             a token is a message
;;;     msg-stage-set, msg-set-is-set             sethood                                 [kept]
;;;     msg-lists-are-lists                       a list of messages is a list (TUPLES(SET))
;;;     list-in-some-stage                        a list of messages sits in TUPLES of ONE stage
;;;                                               (list induction: the finitely many component
;;;                                               stages have a common bound)
;;;     list-in-msgs                              a list of messages is a message
;;;  4. token-set-is-set, token-not-list          THE TOKEN LAW, read off IS-TOKEN-SET
;;;     msg-induction                             STRUCTURAL INDUCTION, class form          [kept]
;;;     msg-cases                                 a message is a token or a list            [kept]
;;;     msg-cases-disjoint                        ... and not both (the token law)
;;;  5. pair-in-cartesian-parts, subterm-rel-unfold, subterm-in-msgs, subterm-least,
;;;     subterm-refl, subterm-component           the clauses, minimality
;;;     subterm-cases (INVERSION), subterm-trans, subterm-of-token, subterm-of-list,
;;;     token-subterm-of-list
;;;  6. msg-rank-prop, msg-stage-list-inv, msg-rank-token, msg-rank-component,
;;;     subterm-rank, subterm-antisym             the rank; the subterm relation is a partial order
;;;
;;; THE TECHNIQUE (S-1's, kept).  (a) A stage hypothesis is opened on a LANE: the claim
;;; (IN m BODY) is proved by rewriting BODY back to the stage term (there is no hypothesis-side
;;; subst).  (b) Every property of the subterm relation that is not one of its two clauses is
;;; ONE device: `subterm-least' at the separation
;;;     RR = { p in SUBTERM-REL(T) : exists u, v. p = [u, v] and COND(u, v) },
;;; shown to be in POWER(A x A) (a set, as T is) and closed under the two clauses; then every
;;; subterm pair satisfies COND.  COND is the inversion disjunction for subterm-cases, "every
;;; subterm of u is one of v" for subterm-trans, "u = v or rank u < rank v" for subterm-rank.
;;; `sml-closed-pairs!' reduces each closure obligation to the one fact the new pair needs.
;;; (c) The rank is an IOTA: `iota-d' with existence from nn-least-element over the stage indices
;;; holding m, uniqueness from nn-le-antisym.
;;;
;;; TYPE BEFORE YOU INSTANTIATE: a predicate hypothesis IS-SUBTERM(T, a, NTH(i, l)) does not
;;; certify NTH(i, l) as defined, so every component is typed by `nth-in-range' before anything
;;; is instantiated at it.
;;;
;;; WHAT CHANGED FROM S-1 (the table is in scratchpad/triage/WEEK3-REPORTS.md, S-2): the three
;;; constructors and their freeness (9 theorems) are gone -- a token is itself, a list is a
;;; TUPLES member, and "two lists with equal components are equal" is `tuple-extensionality'
;;; (theorem-library/tuple-extensionality.scm), cited as it stands; the keys, KINV and
;;; MESSAGE-ALGEBRA (6) are gone; Proposition 2.12 (keys) is gone; the binary rank laws became
;;; one n-ary law, `msg-rank-component', which needs the TOKEN LAW (a list of rank 0 would be a
;;; token); `list-in-some-stage' is new: an n-ary list's components sit in finitely many stages
;;; and need a common bound, which S-1's binary CAT got from one addition.
;;;
;;; LOAD WINDOW: after theorem-library/tuples-induction, theorem-library/matof-in-mat
;;; (tuples-mono), theorem-library/nn-least-element (the latest citation), pair-tuple-sethood,
;;; nn-order-proof, nn-order-ord, rr-order-basics; structure-library/strand-messages before it.
;;; The present slot (load.scm, after integral-laws) satisfies all of them.

;;; -----------------------------------------------------------------------
;;; helpers (prefix sml-)

;; `keep' the named formulas and close by `prop' -- unless `keep' found the kept
;; sequent already proven, which GROUNDS the focus leaf.
(define (sml-keep-prop! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply dk-only! fs)
    (if (not (sequent-node-grounded? node)) (prop))))

;; (= L1 L2) in context, L1 and L2 literal lists of one length; the goal (= x y) with x
;; the I-th entry of L1 and y the I-th entry of L2.
(define (sml-component! l1 l2 i)
  (let* ((x (list-ref l1 i)) (y (list-ref l2 i)))
    (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
    (subst `(= ,y (NTH ,i ,l2)))
    (subst `(= ,l2 ,l1))
    (nth-r)
    (rfl)))

;; Skolemise the FORSOME EX in context and every FORSOME that lands from it, outermost
;; first; returns the eigenvariables in order.
(define (sml-unpack! ex)
  (let loop ((ex ex) (acc '()))
    (let* ((before (dk-asms))
           (v (dk-skolem! ex))
           (new (filter (lambda (f) (not (member f before))) (dk-asms)))
           (next (find-first (lambda (f) (dk-head-is? f 'FORSOME)) new)))
      (if next (loop next (cons v acc)) (reverse (cons v acc))))))

;; (IN x (CARTESIAN C1 ... Cn)) in context: land and return the existential chain the
;; primitive `cartesian-decompose' schema reads it as, with FIXED binders cdv1_ ...
(define (sml-cart-chain x classes)
  (let nest ((i 1) (cs classes) (vars '()))
    (if (null? cs)
        `(= ,x (LIST ,@(reverse vars)))
        (let ((v (string->symbol (string-append "cdv" (number->string i) "_"))))
          `(FORSOME ,v (AND (IN ,v ,(car cs)) ,(nest (+ i 1) (cdr cs) (cons v vars))))))))

(define (sml-cart-open! mem)
  (let* ((ex  (sml-cart-chain (cadr mem) (cdr (caddr mem))))
         (imp `(IMPLIES ,mem ,ex)))
    (dk-have! imp (lambda () (mac 'cartesian-decompose) (di) (ass)))
    (detach! imp)
    (or (dk-ctx-form ex) (error "sml-cart-open!: the chain did not land" (expression->string ex)))))

;; (IN x (UNION A B)) in context: land and return (OR (IN x A) (IN x B)).
(define (sml-union-open! mem)
  (let* ((x (cadr mem)) (a (cadr (caddr mem))) (b (caddr (caddr mem)))
         (o `(OR (IN ,x ,a) (IN ,x ,b))))
    (dk-have! o (lambda () (fact 'union-membership a b x) (sml-keep-prop! (iff-for mem) mem)))
    o))

;; The goal (IN x (UNION A B)) with (IN x A) (LEFT? true) or (IN x B) in context.
(define (sml-union-in! left?)
  (let* ((g (dk-goal)) (x (cadr g)) (a (cadr (caddr g))) (b (caddr (caddr g))))
    (fact 'union-membership a b x)
    (sml-keep-prop! (iff-for g) `(IN ,x ,(if left? a b)))))

;; The stage equation at n (n = 0, or (succ j) with j in NN in context), landed and returned.
(define (sml-stage-eq tt n)
  (if (equal? n 0)
      (dk-cite! 'msg-stage-zero tt)
      (dk-cite! 'msg-stage-succ tt (cadr n))))

;; (IN m (MSG-STAGE tt n)) in context: land and return (IN m BODY), BODY the right-hand
;; side of the stage equation.
(define (sml-stage-open! m tt n)
  (let* ((eqn (sml-stage-eq tt n))
         (body (caddr eqn))
         (claim `(IN ,m ,body)))
    (dk-have! claim (lambda () (subst `(= ,body (MSG-STAGE ,tt ,n))) (ass)))
    claim))

;; Is G the step case of an `ni' on a guarded NN universal?
(define (sml-step-case? g)
  (and (dk-head-is? g 'FORALL) (dk-head-is? (caddr g) 'IMPLIES)
       (dk-head-is? (cadr (caddr g)) 'IN) (eq? (caddr (cadr (caddr g))) 'NN)))

;; (IN (NTH i l) C) from i in NN, l in TUPLES(C), 1 <= i, i <= LENGTH(l) in context.
(define (sml-nth-in! cc i l)
  (let ((goal `(IN (NTH ,i ,l) ,cc)))
    (if (not (dk-asm? goal))
        (begin
          (dk-have! `(AND (IN ,i NN) (AND (IN ,l (TUPLES ,cc)) (AND (<= 1 ,i) (<= ,i (LENGTH ,l)))))
            (lambda () (dk-conj-close! dk-ass!)))
          (fact 'nth-in-range cc i l)))
    goal))

;;; -----------------------------------------------------------------------
;;; 1. A set is the only member of its own singleton PAIR(a, a).

(sp (make-wff '(FORALL a (IMPLIES (IN a SET) (IN a (PAIR a a))))))
(di)
(dk-have! '(AND (IN a SET) (IN a SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing-membership 'a 'a)
(inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-head-is? (caddr f) 'IFF)))
                 "the pairing universal")
        'a)
(dk-have! '(OR (= a a) (= a a)) (lambda () (oi-l) (rfl)))
(sml-keep-prop! (iff-for '(IN a (PAIR a a))) '(OR (= a a) (= a a)))
(qed 'pair-self-member)

(sp (make-wff '(FORALL a (FORALL x (IMPLIES (IN a SET) (IMPLIES (IN x (PAIR a a)) (= x a)))))))
(di) (di) (di)
(dk-have! '(AND (IN a SET) (IN a SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing-membership 'a 'a)
(inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-head-is? (caddr f) 'IFF)))
                 "the pairing universal")
        'x)
(sml-keep-prop! (iff-for '(IN x (PAIR a a))) '(IN x (PAIR a a)))
(qed 'pair-self-eq)

;;; -----------------------------------------------------------------------
;;; 2. The stages.

(sp (make-wff '(FORALL T (FORALL tk (IMPLIES (IN tk T) (IN tk (MSG-STAGE T 0)))))))
(dk-peel!)
(subst (sml-stage-eq 'T 0))
(ass)
(qed 'msg-stage-token)

(sp (make-wff '(FORALL T (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T n)) (IN m (MSG-STAGE T (succ n))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T '(succ n)))
(sml-union-in! #t)
(qed 'msg-stage-keep)

(sp (make-wff '(FORALL T (FORALL n (FORALL l
   (IMPLIES (IN n NN) (IMPLIES (IN l (TUPLES (MSG-STAGE T n))) (IN l (MSG-STAGE T (succ n))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T '(succ n)))
(sml-union-in! #f)
(qed 'msg-stage-list)

(sp (make-wff '(FORALL T (FORALL m (IMPLIES (IN m (MSG-STAGE T 0)) (IN m T))))))
(dk-peel!)
(sml-stage-open! 'm 'T 0)
(qed 'msg-stage-zero-elim)

(sp (make-wff '(FORALL T (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T (succ n)))
     (OR (IN m (MSG-STAGE T n)) (IN m (TUPLES (MSG-STAGE T n)))))))))))
(dk-peel!)
(sml-union-open! (sml-stage-open! 'm 'T '(succ n)))
(qed 'msg-stage-succ-cases)

;;; S_j is included in S_(j + d).  The induction variable d is OUTERMOST, as `ni' needs it.
(sp (make-wff '(FORALL d (IMPLIES (IN d NN)
   (FORALL T (FORALL j (FORALL m
     (IMPLIES (IN j NN) (IMPLIES (IN m (MSG-STAGE T j)) (IN m (MSG-STAGE T (+ j d))))))))))))
(define sml-cases (dk-opened (lambda () (ni))))
(define (sml-case! pred)
  (dk-focus! (or (find-first (lambda (l) (pred (dk-goal-of l))) sml-cases)
                 (error "sml-case!: no such case"))))
;; base: j + 0 = j
(sml-case! (lambda (g) (not (sml-step-case? g))))
(dk-peel!)
(subst (dk-cite! 'nn-add-zero 'j))
(ass)
;; step: j + succ n = succ (j + n), the hypothesis at j, then one more stage
(sml-case! sml-step-case?)
(let* ((landed (dk-peel!))
       (ih (or (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed)
               (error "msg-stage-add: no induction hypothesis")))
       (g (dk-goal))                          ; (IN m (MSG-STAGE T (+ j (succ n))))
       (m (cadr g)) (stage (caddr g))
       (tt (cadr stage)) (sum (caddr stage))
       (j (cadr sum)) (n (cadr (caddr sum))))
  (subst (dk-cite! 'nn-add-succ j n))
  (dk-have! `(AND (IN ,j NN) (IN ,n NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'nn-add-closed j n)
  (dk-apply! ih tt j m)
  (fact 'msg-stage-keep tt `(+ ,j ,n) m)
  (ass))
(qed 'msg-stage-add)

;;; -----------------------------------------------------------------------
;;; 3. The message set.

(sp (make-wff '(FORALL T (== (MSG-SET T) (BIG-UNION n NN (MSG-STAGE T n))))))
(di) (mac 'MSG-SET) (qrfl)
(qed 'msg-set-unfold)

(sp (make-wff '(FORALL T (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T n)) (IN m (MSG-SET T)))))))))
(dk-peel!)
(mac 'MSG-SET)
(dk-each-leaf! (lambda () (bu-mi 'n)) (lambda () (ass)))
(qed 'msg-set-intro)

(sp (make-wff '(FORALL T (FORALL m
   (IMPLIES (IN m (MSG-SET T)) (FORSOME n (AND (IN n NN) (IN m (MSG-STAGE T n)))))))))
(dk-peel!)
(let* ((eqn (dk-cite! 'msg-set-unfold 'T))
       (bu `(IN m ,(caddr eqn))))
  (dk-have! bu (lambda () (subst `(= ,(caddr eqn) (MSG-SET T))) (ass)))
  (let ((before (dk-asms)))
    (bu-me bu)
    (let ((typ (find-first (lambda (f) (and (not (member f before)) (dk-head-is? f 'IN)
                                            (eq? (caddr f) 'NN)))
                           (dk-asms))))
      (ew (cadr typ))
      (dk-conj-close! (lambda () (ass))))))
(qed 'msg-set-elim)

;; (IN x (MSG-SET tt)) in context: land a stage index and the stage membership; return the index.
(define (sml-set-open! x tt)
  (dk-skolem! (dk-cite! 'msg-set-elim tt x)))

(sp (make-wff '(FORALL T (FORALL tk (IMPLIES (IN tk T) (IN tk (MSG-SET T)))))))
(dk-peel!)
(fact 'msg-stage-token 'T 'tk)
(fact 'nn-zero-in)
(fact 'msg-set-intro 'T 0 'tk)
(ass)
(qed 'token-in-msgs)

;; The focus goal (IN X SET) for X a UNION / TUPLES / CARTESIAN of sets in context.
(define (sml-set! t)
  (let ((goal `(IN ,t SET)))
    (cond
      ((dk-asm? goal) goal)
      ((and (pair? t) (eq? (car t) 'UNION))
       (sml-set! (cadr t)) (sml-set! (caddr t))
       (dk-have! `(AND (IN ,(cadr t) SET) (IN ,(caddr t) SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
       (fact 'union-set-closure (cadr t) (caddr t))
       goal)
      ((and (pair? t) (eq? (car t) 'TUPLES))
       (sml-set! (cadr t))
       (fact 'tuples-sethood (cadr t))
       goal)
      ((and (pair? t) (eq? (car t) 'CARTESIAN) (= (length t) 3))
       (sml-set! (cadr t)) (sml-set! (caddr t))
       (let ((both `(AND (IN ,(cadr t) SET) (IN ,(caddr t) SET))))
         (dk-have! both (lambda () (dk-conj-close! (lambda () (ass)))))
         (fact 'cartesian-set-iff (cadr t) (caddr t))
         (dk-have! goal (lambda () (sml-keep-prop! (iff-for goal) both)))
         goal))
      (else (error "sml-set!: no route to the sethood of" (expression->string t))))))

(define (sml-set-close!)
  (let ((g (dk-goal)))
    (sml-set! (cadr g))
    (if (and (alpha-equiv? (dk-goal) g) (dk-asm? g)) (ass))))

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL T (IMPLIES (IN T SET) (IN (MSG-STAGE T n) SET)))))))
(define sml-cases2 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases2))
(dk-peel!)
(subst (sml-stage-eq 'T 0))
(ass)
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases2))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (stage (cadr (dk-goal)))
       (tt (cadr stage)) (n (cadr (caddr stage))))
  (dk-apply! ih tt)
  (subst (sml-stage-eq tt `(succ ,n)))
  (sml-set-close!))
(qed 'msg-stage-set)

(sp (make-wff '(FORALL T (IMPLIES (IN T SET) (IN (MSG-SET T) SET)))))
(dk-peel!)
(mac 'MSG-SET)
(dk-each-leaf! (lambda () (bu-set))
  (lambda ()
    (if (dk-head-is? (dk-goal) 'IN)
        (begin (fact 'nn-is-set) (ass))
        (begin (dk-peel!)
               (fact 'msg-stage-set (caddr (cadr (dk-goal))) 'T)
               (ass)))))
(qed 'msg-set-is-set)

;; "C1 inside C2" as the universal tuples-mono wants, proved by THUNK on the peeled leaf
;; (the eigenvariable is read off the goal and handed to THUNK).
(define (sml-incl! c1 c2 thunk)
  (let ((incl `(FORALL smw_ (IMPLIES (IN smw_ ,c1) (IN smw_ ,c2)))))
    (dk-have! incl (lambda () (dk-peel!) (thunk (cadr (dk-goal)))))
    incl))

;; (IN l (TUPLES c2)) from (IN l (TUPLES c1)) in context, by tuples-mono with the inclusion
;; proved by THUNK.
(define (sml-tuples-lift! l c1 c2 thunk)
  (sml-incl! c1 c2 thunk)
  (dk-apply! (dk-cite! 'tuples-mono c1 c2) l))

(sp (make-wff '(FORALL T (FORALL l
   (IMPLIES (IN l (TUPLES (MSG-SET T))) (IN l (TUPLES SET)))))))
(dk-peel!)
(sml-tuples-lift! 'l '(MSG-SET T) 'SET
  (lambda (w) (fact 'membership-implies-sethood w '(MSG-SET T)) (ass)))
(ass)
(qed 'msg-lists-are-lists)

;;; A list of messages has all its components in ONE stage: list induction (tuples-induction)
;;; at the class of the lists that do; the CONS step lifts the head's stage and the tail's to
;;; their sum (msg-stage-add, tuples-mono).
(define sml-lis-class
  '(SEP smy_ (TUPLES (MSG-SET T))
        (FORSOME smk_ (AND (IN smk_ NN) (IN smy_ (TUPLES (MSG-STAGE T smk_)))))))

(sp (make-wff '(FORALL T (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T)))
   (FORSOME n (AND (IN n NN) (IN l (TUPLES (MSG-STAGE T n))))))))))
(dk-peel!)
(let* ((ind0 (lookup-theorem 'tuples-induction))
       (ind (subst-free (quantifier-var (quantifier-body ind0)) sml-lis-class
              (quantifier-body (subst-free (quantifier-var ind0) '(MSG-SET T) (quantifier-body ind0)))))
       (prem (cadr ind))
       (h-base (cadr prem))
       (h-step (caddr prem)))
  (dk-have! h-base
    (lambda ()
      (in-sep! (lambda () (fact 'empty-in-tuples '(MSG-SET T)) (ass))
               (lambda ()
                 (ew 0)
                 (dk-conj-close!
                   (lambda ()
                     (if (equal? (cadr (dk-goal)) 0)
                         (begin (fact 'nn-zero-in) (ass))
                         (begin (subst (sml-stage-eq 'T 0))   ; MSG-STAGE(T, 0) is not
                                (fact 'empty-in-tuples 'T)        ; certified defined; T is
                                (ass)))))))))
  (dk-have! h-step
    (lambda ()
      (dk-peel!)
      (dk-split-all!)
      (let* ((g (dk-goal))                          ; (IN (CONS x M) C)
             (x (cadr (cadr g))) (mm (caddr (cadr g)))
             (j (begin (sep-me `(IN ,mm ,sml-lis-class))
                       (dk-skolem! (find-first (lambda (f) (and (dk-head-is? f 'FORSOME)
                                                                (dk-contains? f mm)))
                                               (dk-asms)))))
             (i (sml-set-open! x 'T))
             (sij `(MSG-STAGE T (+ ,i ,j))))
        (dk-have! `(AND (IN ,i NN) (IN ,j NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
        (fact 'nn-add-closed i j)
        (fact 'msg-stage-add j 'T i x)                   ; x in S_(i + j)
        (sml-tuples-lift! mm `(MSG-STAGE T ,j) sij
          (lambda (w)
            (fact 'msg-stage-add i 'T j w)                ; w in S_(j + i)
            (fact 'nn-add-comm i j)
            (subst `(= (+ ,i ,j) (+ ,j ,i)))
            (ass)))
        (dk-have! `(AND (IN ,x ,sij) (IN ,mm (TUPLES ,sij))) (lambda () (dk-conj-close! (lambda () (ass)))))
        (fact 'cons-in-tuples sij x mm)
        (in-sep! (lambda ()
                   (dk-have! `(AND (IN ,x (MSG-SET T)) (IN ,mm (TUPLES (MSG-SET T))))
                     (lambda () (dk-conj-close! (lambda () (ass)))))
                   (fact 'cons-in-tuples '(MSG-SET T) x mm)
                   (ass))
                 (lambda ()
                   (ew `(+ ,i ,j))
                   (dk-conj-close! (lambda () (ass))))))))
  (dk-have! prem (lambda () (dk-conj-close! (lambda () (ass)))))
  (let ((all (dk-cite! 'tuples-induction '(MSG-SET T) sml-lis-class)))
    (dk-apply! all 'l)
    (sep-me `(IN l ,sml-lis-class))
    (ass)))
(qed 'list-in-some-stage)

(sp (make-wff '(FORALL T (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T))) (IN l (MSG-SET T)))))))
(dk-peel!)
(let ((n (dk-skolem! (dk-cite! 'list-in-some-stage 'T 'l))))
  (fact 'msg-stage-list 'T n 'l)
  (fact 'nn-succ-closed n)
  (fact 'msg-set-intro 'T `(succ ,n) 'l)
  (ass))
(qed 'list-in-msgs)

;;; -----------------------------------------------------------------------
;;; 4. The token law, structural induction, the two cases.

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T) (IN T SET)))))
(dk-peel!)
(mac-h 'is-token-set '(IS-TOKEN-SET T))
(dk-split-all!)
(ass)
(qed 'token-set-is-set)

;; (NOT (IN x (TUPLES SET))) from (IS-TOKEN-SET tt) and (IN x tt) in context, on a lane.
(define (sml-token-law! tt x)
  (let ((claim `(NOT (IN ,x (TUPLES SET)))))
    (dk-have! claim
      (lambda ()
        (mac-h 'is-token-set `(IS-TOKEN-SET ,tt))
        (dk-split-all!)
        (dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'TUPLES)))
                            "the token law")
                   x)
        (ass)))
    claim))

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
   (FORALL tk (IMPLIES (IN tk T) (NOT (IN tk (TUPLES (MSG-SET T))))))))))
(dk-peel!)
(let ((nl (sml-token-law! 'T 'tk)))
  (di)
  (fact 'msg-lists-are-lists 'T 'tk)
  (ai nl))
(qed 'token-not-list)

;; The two hypotheses of msg-induction at the class CC (read off the theorem, so that
;; the driver's spelling cannot drift from the statement's).
(define (sml-ind-hyps tt cc)
  (let* ((th (lookup-theorem 'msg-induction))
         (b1 (subst-free (quantifier-var th) tt (quantifier-body th)))
         (b2 (subst-free (quantifier-var b1) cc (quantifier-body b1))))
    (list (cadr b2) (cadr (caddr b2)))))

(sp (make-wff '(FORALL T (FORALL C
   (IMPLIES (FORALL tk (IMPLIES (IN tk T) (IN tk C)))
   (IMPLIES (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T)))
              (IMPLIES (FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
                                    (IN (NTH i l) C)))))
                       (IN l C))))
     (FORALL m (IMPLIES (IN m (MSG-SET T)) (IN m C)))))))))
(let* ((landed (dk-peel!))
       (g0 (dk-goal)) (m0 (cadr g0)) (cc (caddr g0)) (tt 'T)
       (h-tok (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (not (dk-contains? f 'TUPLES)))) landed)
                  (error "msg-induction: no token hypothesis")))
       (h-list (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'TUPLES))) landed)
                   (error "msg-induction: no list hypothesis")))
       (claim `(FORALL smn_ (IMPLIES (IN smn_ NN)
                 (FORALL smm_ (IMPLIES (IN smm_ (MSG-STAGE ,tt smn_)) (IN smm_ ,cc)))))))
  (dk-have! claim
    (lambda ()
      (let ((cases (dk-opened (lambda () (ni)))))
        ;; base: a member of stage 0 is a token
        (dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) cases))
        (dk-peel!)
        (let ((m (cadr (dk-goal))))
          (fact 'msg-stage-zero-elim tt m)
          (dk-apply! h-tok m)
          (ass))
        ;; step: a member of stage succ n is kept, or a list of stage-n messages
        (dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) cases))
        (let* ((landed (dk-peel!))
               (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
               (m (cadr (dk-goal)))
               (n (cadr (caddr (caddr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) m)))
                                                  landed)))))
               (sn `(MSG-STAGE ,tt ,n))
               (o (dk-cite! 'msg-stage-succ-cases tt n m)))
          (dk-each-leaf! (lambda () (ai o))
            (lambda ()
              (if (dk-asm? `(IN ,m ,sn))
                  (begin (dk-apply! ih m) (ass))
                  (let ((comps `(FORALL smi_ (IMPLIES (IN smi_ NN) (IMPLIES (<= 1 smi_)
                                   (IMPLIES (<= smi_ (LENGTH ,m)) (IN (NTH smi_ ,m) ,cc)))))))
                    (sml-tuples-lift! m sn `(MSG-SET ,tt)
                      (lambda (w) (fact 'msg-set-intro tt n w) (ass)))
                    (dk-have! comps
                      (lambda ()
                        (dk-peel!)
                        (let ((i (cadr (cadr (dk-goal)))))
                          (sml-nth-in! sn i m)
                          (dk-apply! ih `(NTH ,i ,m))
                          (ass))))
                    (dk-apply! h-list m)
                    (ass)))))))))
  ;; the message is in some stage, and the claim holds there
  (let ((n (sml-set-open! m0 tt)))
    (dk-apply! claim n m0)
    (ass)))
(qed 'msg-induction)

(sp (make-wff '(FORALL T (FORALL m (IMPLIES (IN m (MSG-SET T))
   (OR (IN m T) (IN m (TUPLES (MSG-SET T)))))))))
(dk-peel!)
(let* ((cc '(SEP smz_ (MSG-SET T) (OR (IN smz_ T) (IN smz_ (TUPLES (MSG-SET T))))))
       (hs (sml-ind-hyps 'T cc)))
  (dk-have! (car hs)
    (lambda ()
      (dk-peel!)
      (let ((x (cadr (dk-goal))))
        (in-sep! (lambda () (fact 'token-in-msgs 'T x) (ass))
                 (lambda () (oi-l) (ass))))))
  (dk-have! (cadr hs)
    (lambda ()
      (dk-peel!)
      (let ((x (cadr (dk-goal))))
        (in-sep! (lambda () (fact 'list-in-msgs 'T x) (ass))
                 (lambda () (oi-r) (ass))))))
  (dk-apply! (dk-cite! 'msg-induction 'T cc) 'm)
  (sep-me `(IN m ,cc))
  (ass))
(qed 'msg-cases)

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T) (FORALL m
   (NOT (AND (IN m T) (IN m (TUPLES (MSG-SET T))))))))))
(dk-peel!)
(di)
(dk-split-all!)
(fact 'token-not-list 'T 'm)
(ai '(NOT (IN m (TUPLES (MSG-SET T)))))
(qed 'msg-cases-disjoint)

;;; -----------------------------------------------------------------------
;;; 5. The subterm relation: its two clauses, minimality, inversion.

(sp (make-wff '(FORALL X (FORALL Y (FORALL u (FORALL v
   (IMPLIES (IN (LIST u v) (CARTESIAN X Y)) (AND (IN u X) (IN v Y)))))))))
(dk-peel!)
(let* ((vs (sml-unpack! (sml-cart-open! '(IN (LIST u v) (CARTESIAN X Y)))))
       (c1 (car vs)) (c2 (cadr vs))
       (eqn (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) '(LIST u v)))) (dk-asms))))
  (dk-have! `(= u ,c1) (lambda () (sml-component! '(LIST u v) (caddr eqn) 1)))
  (dk-have! `(= v ,c2) (lambda () (sml-component! '(LIST u v) (caddr eqn) 2)))
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (if (equal? (cadr (dk-goal)) 'u) (subst `(= u ,c1)) (subst `(= v ,c2)))
      (ass))))
(qed 'pair-in-cartesian-parts)

(sp (make-wff '(FORALL T (== (SUBTERM-REL T)
   (SEP p_ (CARTESIAN (MSG-SET T) (MSG-SET T))
        (FORALL q_ (IMPLIES (IN q_ (POWER (CARTESIAN (MSG-SET T) (MSG-SET T))))
                            (IMPLIES (IS-SUBTERM-CLOSED T q_) (IN p_ q_)))))))))
(di) (mac 'SUBTERM-REL) (qrfl)
(qed 'subterm-rel-unfold)

(define (sml-msgs tt) `(MSG-SET ,tt))
(define (sml-box tt) `(CARTESIAN (MSG-SET ,tt) (MSG-SET ,tt)))

;; (IS-SUBTERM tt a b) in context, b TYPED or a variable: land (IN a A), (IN b A) and the
;; universal "every closed q in POWER(A x A) holds [a, b]", which is returned.
(define (sml-st-open! tt a b)
  (let* ((hyp `(IS-SUBTERM ,tt ,a ,b))
         (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt)))
         (eqn (dk-cite! 'subterm-rel-unfold tt))
         (sepm `(IN (LIST ,a ,b) ,(caddr eqn))))
    (dk-have! mem (lambda () (fact 'is-subterm tt a b) (sml-keep-prop! (iff-for hyp) hyp)))
    (dk-have! sepm (lambda () (subst `(= ,(caddr eqn) (SUBTERM-REL ,tt))) (ass)))
    (let* ((landed (dk-landed (lambda () (sep-me sepm))))
           (univ (or (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed)
                     (error "sml-st-open!: no universal landed"))))
      (fact 'pair-in-cartesian-parts (sml-msgs tt) (sml-msgs tt) a b)
      (dk-split-all!)
      univ)))

;; The kind of a clause of IS-SUBTERM-CLOSED, by its binders: reflexivity binds one
;; variable, the list clause three (a test on the body would read the relation, which
;; may itself mention NTH).
(define (sml-clause-kind f)
  (let loop ((f f) (k 0))
    (if (dk-head-is? f 'FORALL) (loop (caddr f) (+ k 1)) (if (>= k 3) 'list 'refl))))

;; The goal (IS-SUBTERM tt a b) with (IN a A), (IN b A) in context.  STEP is called on the
;; lane where q is a closed relation in POWER(A x A), with the two clauses of q's
;; closedness split into the context, as (STEP q CLAUSE-OF); it must close (IN [a, b] q).
;; PRE is run first with q (a universal that must be cited at q is cited there).
(define (sml-st-intro! tt a b pre step)
  (mac 'is-subterm)
  (mac 'SUBTERM-REL)
  (in-sep! (lambda () (fact 'pair-in-cartesian (sml-msgs tt) (sml-msgs tt) a b) (ass))
           (lambda ()
             (dk-peel!)
             (let* ((q (caddr (dk-goal)))
                    (closed `(IS-SUBTERM-CLOSED ,tt ,q)))
               (pre q)
               (mac-h 'is-subterm-closed closed)
               (dk-split-all!)
               (let ((clause-of (lambda (kind)
                                  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL)
                                                                   (dk-contains? f q)
                                                                   (eq? (sml-clause-kind f) kind)))
                                                  (dk-asms))
                                      (error "sml-st-intro!: no clause" kind)))))
                 (step q clause-of))))))

(sp (make-wff '(FORALL T (FORALL a (FORALL b
   (IMPLIES (IS-SUBTERM T a b) (AND (IN a (MSG-SET T)) (IN b (MSG-SET T)))))))))
(dk-peel!)
(sml-st-open! 'T 'a 'b)
(dk-conj-close! (lambda () (ass)))
(qed 'subterm-in-msgs)

(sp (make-wff '(FORALL T (FORALL r
   (IMPLIES (IN r (POWER (CARTESIAN (MSG-SET T) (MSG-SET T))))
   (IMPLIES (IS-SUBTERM-CLOSED T r)
     (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T a b) (IN (LIST a b) r))))))))))
(dk-peel!)
(dk-apply! (sml-st-open! 'T 'a 'b) 'r)
(ass)
(qed 'subterm-least)

(sp (make-wff '(FORALL T (FORALL a (IMPLIES (IN a (MSG-SET T)) (IS-SUBTERM T a a))))))
(dk-peel!)
(sml-st-intro! 'T 'a 'a (lambda (q) #t)
  (lambda (q clause-of) (dk-apply! (clause-of 'refl) 'a) (ass)))
(qed 'subterm-refl)

;;; A subterm of a component is a subterm of the list.
(sp (make-wff '(FORALL T (FORALL a (FORALL l (FORALL i
   (IMPLIES (IN l (TUPLES (MSG-SET T))) (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
     (IMPLIES (IS-SUBTERM T a (NTH i l)) (IS-SUBTERM T a l))))))))))))
(dk-peel!)
(sml-nth-in! '(MSG-SET T) 'i 'l)
(fact 'list-in-msgs 'T 'l)
(let ((u (sml-st-open! 'T 'a '(NTH i l))))
  (sml-st-intro! 'T 'a 'l
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'list) 'a 'l 'i) (ass))))
(qed 'subterm-component)

;;; -----------------------------------------------------------------------
;;; The one device: subterm-least at a SEP of SUBTERM-REL by a condition on the pair.

(define (sml-st-mem! tt a b)          ; from (IS-SUBTERM tt a b)
  (let ((hyp `(IS-SUBTERM ,tt ,a ,b)) (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt))))
    (dk-have! mem (lambda () (fact 'is-subterm tt a b) (sml-keep-prop! (iff-for hyp) hyp)))
    mem))
(define (sml-st-pred! tt a b)         ; from (IN (LIST a b) (SUBTERM-REL tt))
  (let ((hyp `(IS-SUBTERM ,tt ,a ,b)) (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt))))
    (dk-have! hyp (lambda () (fact 'is-subterm tt a b) (sml-keep-prop! (iff-for hyp) mem)))
    hyp))

;; (IN (SUBTERM-REL tt) SET), from the sethood of T in context.
(define (sml-st-set! tt)
  (let* ((eqn (dk-cite! 'subterm-rel-unfold tt))
         (sepf (caddr eqn))
         (goal `(IN (SUBTERM-REL ,tt) SET)))
    (fact 'msg-set-is-set tt)
    (dk-have! `(IN ,sepf SET) (lambda () (dk-each-leaf! (lambda () (sep-set)) (lambda () (sml-set-close!)))))
    (dk-have! goal (lambda () (subst eqn) (ass)))
    goal))

;; The goal (IN RR (POWER (A x A))) for RR a SEP over SUBTERM-REL(tt).
(define (sml-subrel-power! tt rr)
  (sml-st-set! tt)
  (mac 'power-set-membership)
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (if (dk-head-is? (dk-goal) 'IN)
          (dk-each-leaf! (lambda () (sep-set)) (lambda () (ass)))
          (let* ((landed (dk-peel!))
                 (z (cadr (dk-goal)))
                 (eqn (dk-cite! 'subterm-rel-unfold tt))
                 (sepf (caddr eqn)))
            (sep-me `(IN ,z ,rr))
            (dk-have! `(IN ,z ,sepf) (lambda () (subst `(= ,sepf (SUBTERM-REL ,tt))) (ass)))
            (sep-me `(IN ,z ,sepf))
            (ass))))))

(define (sml-pair-cond p cond2)          ; exists u, v. p = [u, v] and COND2(u, v)
  `(FORSOME siu_ (FORSOME siv_ (AND (= ,p (LIST siu_ siv_)) ,(cond2 'siu_ 'siv_)))))

;; (IN [a, b] RR) in context, RR = (SEP v ST (pair-cond v COND2)): land COND2(a, b).
(define (sml-pair-cond-open! rr a b cond2)
  (sep-me `(IN (LIST ,a ,b) ,rr))
  (sml-pair-cond-unpack! a b cond2))

(define (sml-pair-cond-unpack! a b cond2)
  (let* ((ex (or (find-first (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f `(LIST ,a ,b))))
                             (dk-asms))
                 (error "sml-pair-cond-open!: no pair condition landed")))
         (vs (sml-unpack! ex))
         (u (car vs)) (v (cadr vs))
         (claim (cond2 a b)))
    (dk-have! `(= ,a ,u) (lambda () (sml-component! `(LIST ,a ,b) `(LIST ,u ,v) 1)))
    (dk-have! `(= ,b ,v) (lambda () (sml-component! `(LIST ,a ,b) `(LIST ,u ,v) 2)))
    (dk-have! claim (lambda () (subst `(= ,a ,u)) (subst `(= ,b ,v)) (ass)))
    claim))

;; The goal (IN [a, b] RR): the domain by IS-SUBTERM (in context), the condition by
;; witnesses a, b and COND-THUNK on COND2(a, b).
(define (sml-pair-cond-intro! tt a b cond-thunk)
  (sml-st-mem! tt a b)
  (in-sep! (lambda () (ass))
           (lambda ()
             (ew a)
             (ew b)
             (dk-each-leaf! (lambda () (di))
               (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (cond-thunk)))))))

;; The goal (IS-SUBTERM-CLOSED tt RR): unfold, and run (CLOSE KIND x c PREV I) on the
;; condition leaf of each clause's new pair [x, c]: PREV is the pair's predecessor
;; NTH(I, c) for the list clause (#f for reflexivity).  On that leaf IS-SUBTERM of both
;; pairs, the typings of x, c, PREV and the list hypotheses are in context.
(define (sml-closed-pairs! tt rr close)
  (mac 'is-subterm-closed)
  (dk-conj-close!
    (lambda ()
      (let ((kind (sml-clause-kind (dk-goal))))
        (dk-peel!)
        (let* ((pr (cadr (dk-goal))) (x (cadr pr)) (c (caddr pr)))
          (case kind
            ((refl)
             (fact 'subterm-refl tt x)
             (sml-pair-cond-intro! tt x x (lambda () (close kind x c #f #f))))
            (else
             (let* ((prevmem (or (find-first (lambda (f) (and (dk-head-is? f 'IN) (alpha-equiv? (caddr f) rr)
                                                               (dk-head-is? (cadr f) 'LIST)
                                                               (equal? (cadr (cadr f)) x)
                                                               (dk-head-is? (caddr (cadr f)) 'NTH)
                                                               (equal? (caddr (caddr (cadr f))) c)))
                                             (dk-asms))
                                 (error "sml-closed-pairs!: no predecessor pair" (expression->string (dk-goal)) (map expression->string (dk-asms)))))
                    (prev (caddr (cadr prevmem)))
                    (i (cadr prev)))
               (sep-me prevmem)
               (sml-nth-in! (sml-msgs tt) i c)
               (sml-st-pred! tt x prev)
               (fact 'list-in-msgs tt c)
               (fact 'subterm-component tt x c i)
               (fact 'subterm-in-msgs tt x prev)
               (dk-split-all!)
               (sml-pair-cond-intro! tt x c (lambda () (close kind x c prev i)))))))))))

;; Run the device: RR from COND2, prove it a member of the power set and closed (CLOSE as in
;; sml-closed-pairs!), cite subterm-least, and land COND2(a, b) from (IS-SUBTERM tt a b).
(define (sml-device! tt a b cond2 close)
  (let ((rr `(SEP sip_ (SUBTERM-REL ,tt) ,(sml-pair-cond 'sip_ cond2))))
    (dk-have! `(IN ,rr (POWER ,(sml-box tt))) (lambda () (sml-subrel-power! tt rr)))
    (dk-have! `(IS-SUBTERM-CLOSED ,tt ,rr) (lambda () (sml-closed-pairs! tt rr close)))
    (fact 'subterm-least tt rr)
    (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                                (not (dk-contains? f 'IS-SUBTERM-CLOSED))))
                               (dk-asms))
                   (error "sml-device!: subterm-least did not detach"))
               a b)
    (sml-pair-cond-open! rr a b cond2)))

;;; INVERSION: a subterm of b is b itself, or b is a list and it is a subterm of a component.
(define (sml-inv tt u v)
  `(OR (= ,u ,v)
       (AND (IN ,v (TUPLES (MSG-SET ,tt)))
            (FORSOME sii_ (AND (IN sii_ NN) (AND (<= 1 sii_) (AND (<= sii_ (LENGTH ,v))
                                                                (IS-SUBTERM ,tt ,u (NTH sii_ ,v)))))))))

(sp (make-wff '(FORALL T (IMPLIES (IN T SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T a b)
    (OR (= a b)
        (AND (IN b (TUPLES (MSG-SET T)))
             (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH b)) (IS-SUBTERM T a (NTH i b)))))))))))))))
(dk-peel!)
(sml-device! 'T 'a 'b (lambda (u v) (sml-inv 'T u v))
  (lambda (kind x c prev i)
    (case kind
      ((refl) (oi-l) (rfl))
      (else (oi-r)
            (dk-conj-close!
              (lambda ()
                (if (dk-head-is? (dk-goal) 'FORSOME)
                    (begin (ew i) (dk-conj-close! (lambda () (ass))))
                    (ass))))))))
(dk-ass!)
(qed 'subterm-cases)

(sp (make-wff '(FORALL T (IMPLIES (IN T SET)
  (FORALL a (FORALL b (FORALL c
    (IMPLIES (IS-SUBTERM T a b) (IMPLIES (IS-SUBTERM T b c) (IS-SUBTERM T a c))))))))))
(dk-peel!)
(let ((cond2 (lambda (u v) `(FORALL sia_ (IMPLIES (IS-SUBTERM T sia_ ,u) (IS-SUBTERM T sia_ ,v))))))
  (dk-apply!
    (sml-device! 'T 'b 'c cond2
      (lambda (kind x c prev i)
        (if (eq? kind 'refl)
            (begin (dk-peel!) (ass))
            (let ((ih (sml-pair-cond-unpack! x prev cond2)))
              (dk-peel!)
              (let ((a1 (caddr (dk-goal))))           ; (IS-SUBTERM T a1 c)
                (dk-apply! ih a1)
                (fact 'subterm-in-msgs 'T a1 prev)
                (dk-split-all!)
                (fact 'subterm-component 'T a1 c i)
                (ass))))))
    'a)
  (ass))
(qed 'subterm-trans)

;; The disjunction subterm-cases lands for (a, b), split: (ON-EQ) with (= a b) in context,
;; (ON-LIST i) with b's list typing, i's typings and IS-SUBTERM(a, NTH(i, b)) in context.
(define (sml-subterm-cases! tt a b on-eq on-list)
  (let ((o (dk-cite! 'subterm-cases tt a b)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? `(= ,a ,b))
            (on-eq)
            (let* ((conj (or (find-first (lambda (f) (and (dk-head-is? f 'AND) (dk-contains? f 'sii_)))
                                         (dk-asms))
                             (dk-pick (lambda (f) (and (dk-head-is? f 'AND) (dk-head-is? (cadr f) 'IN)
                                                       (equal? (cadr (cadr f)) b)))
                                      "the list case")))
                   (parts (dk-split! conj))
                   (ex (find-first (lambda (f) (dk-head-is? f 'FORSOME)) parts))
                   (i (dk-skolem! ex)))
              (on-list i)))))))

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
  (FORALL a (FORALL tk (IMPLIES (IN tk T) (IMPLIES (IS-SUBTERM T a tk) (= a tk)))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(fact 'token-not-list 'T 'tk)
(sml-subterm-cases! 'T 'a 'tk
  (lambda () (ass))
  (lambda (i) (ai '(NOT (IN tk (TUPLES (MSG-SET T)))))))
(qed 'subterm-of-token)

(sp (make-wff '(FORALL T (IMPLIES (IN T SET)
  (FORALL a (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T))) (IMPLIES (IS-SUBTERM T a l)
    (OR (= a l)
        (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH l)) (IS-SUBTERM T a (NTH i l)))))))))))))))
(dk-peel!)
(sml-subterm-cases! 'T 'a 'l
  (lambda () (oi-l) (ass))
  (lambda (i) (oi-r) (ew i) (dk-conj-close! (lambda () (ass)))))
(qed 'subterm-of-list)

;;; A TOKEN that is a subterm of a list is a subterm of one of its components (the token
;;; law rules out the token being the list itself).  The adversary's C case cites this.
(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
  (FORALL tk (FORALL l (IMPLIES (IN tk T) (IMPLIES (IN l (TUPLES (MSG-SET T))) (IMPLIES (IS-SUBTERM T tk l)
    (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH l)) (IS-SUBTERM T tk (NTH i l)))))))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(fact 'token-not-list 'T 'tk)
(sml-subterm-cases! 'T 'tk 'l
  (lambda ()
    (dk-have! '(IN tk (TUPLES (MSG-SET T))) (lambda () (subst '(= tk l)) (ass)))
    (ai '(NOT (IN tk (TUPLES (MSG-SET T))))))
  (lambda (i) (ew i) (dk-conj-close! (lambda () (ass)))))
(qed 'token-subterm-of-list)

;;; -----------------------------------------------------------------------
;;; 6. THE RANK: the least stage holding a message.

(sp (make-wff '(FORALL T (FORALL m (IMPLIES (IN m (MSG-SET T))
   (AND (IN (MSG-RANK T m) NN)
        (AND (IN m (MSG-STAGE T (MSG-RANK T m)))
             (FORALL j (IMPLIES (IN j NN) (IMPLIES (IN m (MSG-STAGE T j)) (<= (MSG-RANK T m) j)))))))))))
(dk-peel!)
(mac 'MSG-RANK)
(define sml-io
  (let find ((e (dk-goal)))
    (cond ((and (pair? e) (eq? (car e) 'IOTA)) e)
          ((pair? e) (or (find (car e)) (find (cdr e))))
          (else #f))))
;; Does F contain an atom (<= X _)?
(define (sml-has-le? f x)
  (and (pair? f)
       (or (and (eq? (car f) '<=) (pair? (cdr f)) (equal? (cadr f) x))
           (any-pred (lambda (g) (sml-has-le? g x)) f))))
(define sml-ss '(SEP smw_ NN (IN m (MSG-STAGE T smw_))))
(define (sml-in-ss! j)                   ; (IN j NN), (IN m (MSG-STAGE T j)) in context
  (dk-have! `(IN ,j ,sml-ss) (lambda () (in-sep! (lambda () (ass)) (lambda () (ass))))))
(dk-each-leaf! (lambda () (iota-d sml-io))
  (lambda ()
    (if (not (dk-head-is? (dk-goal) 'FORSOME))
        (ass)
        (let* ((n0 (sml-set-open! 'm 'T)))
          (dk-have! `(AND (SUBSET ,sml-ss NN) (FORSOME n (IN n ,sml-ss)))
            (lambda ()
              (dk-conj-close!
                (lambda ()
                  (if (dk-head-is? (dk-goal) 'SUBSET)
                      (begin (mac 'subset-def) (dk-peel!) (sep-me `(IN ,(cadr (dk-goal)) ,sml-ss)) (ass))
                      (begin (ew n0) (in-sep! (lambda () (ass)) (lambda () (ass)))))))))
          (let* ((ex (dk-cite! 'nn-least-element sml-ss))
                 (r (dk-skolem! ex))
                 (least (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (sml-has-le? f r)))
                                        (dk-asms))
                            (error "msg-rank-prop: no least-element universal"))))
            (sep-me `(IN ,r ,sml-ss))
            (ew r)
            (dk-each-leaf! (lambda () (di))
              (lambda ()
                (if (dk-head-is? (dk-goal) 'AND)
                    (dk-conj-close!
                      (lambda ()
                        (if (dk-head-is? (dk-goal) 'FORALL)
                            (let* ((landed (dk-peel!)) (j (caddr (dk-goal))))
                              (sml-in-ss! j)
                              (dk-apply! least j)
                              (ass))
                            (ass))))
                    ;; uniqueness: a second least index y is r
                    (let* ((landed (dk-peel!))
                           (y (caddr (dk-goal))))
                      (dk-split-all!)
                      (sml-in-ss! y)
                      (dk-apply! least y)
                      (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL)
                                                                  (sml-has-le? f y)))
                                                 (dk-asms))
                                     (error "msg-rank-prop: no minimality for the second index"))
                                 r)
                      (fact 'nn-le-antisym r y)
                      (ass))))))))))
(qed 'msg-rank-prop)

;;; A list in stage n sits in TUPLES of a strictly earlier stage (the token law: stage 0
;;; holds no list).  Induction on the stage index, outermost.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (FORALL T (IMPLIES (IS-TOKEN-SET T) (FORALL l
   (IMPLIES (IN l (TUPLES SET)) (IMPLIES (IN l (MSG-STAGE T n))
     (FORSOME j (AND (IN j NN) (AND (<= (succ j) n) (IN l (TUPLES (MSG-STAGE T j)))))))))))))))
(define sml-cases3 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases3))
(dk-peel!)
(fact 'msg-stage-zero-elim 'T 'l)
(ai (sml-token-law! 'T 'l))
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases3))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (g (dk-goal))                                       ; the FORSOME
       (mem (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'MSG-STAGE))) landed))
       (l (cadr mem)) (tt (cadr (caddr mem))) (n (cadr (caddr (caddr mem))))
       (o (dk-cite! 'msg-stage-succ-cases tt n l)))
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (if (dk-asm? `(IN ,l (MSG-STAGE ,tt ,n)))
          (let ((j (dk-skolem! (dk-apply! ih tt l))))
            (ew j)
            (dk-conj-close!
              (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn! `(<= (succ ,j) ,n)) (ass)))))
          (begin
            (ew n)
            (dk-conj-close!
              (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn!) (ass)))))))))
(qed 'msg-stage-list-inv)

;; rank-prop at the TYPED message x: land (IN rank NN), (IN x stage(rank)) and the
;; minimality universal; return the rank term.
(define (sml-rank! tt x)
  (fact 'msg-rank-prop tt x)
  (dk-split-all!)
  `(MSG-RANK ,tt ,x))
(define (sml-rank-min x)
  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (sml-has-le? f `(MSG-RANK T ,x)))) (dk-asms))
      (error "sml-rank-min: no minimality for" x)))

(sp (make-wff '(FORALL T (FORALL tk (IMPLIES (IN tk T) (= (MSG-RANK T tk) 0))))))
(dk-peel!)
(fact 'token-in-msgs 'T 'tk)
(fact 'msg-stage-token 'T 'tk)
(fact 'nn-zero-in)
(let ((r (sml-rank! 'T 'tk)))
  (dk-apply! (sml-rank-min 'tk) 0)
  (dk-nn! `(<= ,r 0)))
(qed 'msg-rank-token)

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T) (FORALL l (FORALL i
   (IMPLIES (IN l (TUPLES (MSG-SET T))) (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
     (<= (succ (MSG-RANK T (NTH i l))) (MSG-RANK T l))))))))))))
(dk-peel!)
(fact 'list-in-msgs 'T 'l)
(fact 'msg-lists-are-lists 'T 'l)
(sml-nth-in! '(MSG-SET T) 'i 'l)
(let* ((rl (sml-rank! 'T 'l))
       (rc (sml-rank! 'T '(NTH i l)))
       (j (dk-skolem! (dk-cite! 'msg-stage-list-inv rl 'T 'l))))
  (sml-nth-in! `(MSG-STAGE T ,j) 'i 'l)
  (dk-apply! (sml-rank-min '(NTH i l)) j)
  (dk-nn! `(<= ,rc ,j) `(<= (succ ,j) ,rl)))
(qed 'msg-rank-component)

;;; A proper subterm has a strictly smaller rank; so the subterm relation is ANTISYMMETRIC,
;;; a partial order (reflexive: subterm-refl; transitive: subterm-trans).
(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T a b)
    (OR (= a b) (<= (succ (MSG-RANK T a)) (MSG-RANK T b))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(let ((cond2 (lambda (u v) `(OR (= ,u ,v) (<= (succ (MSG-RANK T ,u)) (MSG-RANK T ,v))))))
  (sml-device! 'T 'a 'b cond2
    (lambda (kind x c prev i)
      (if (eq? kind 'refl)
          (begin (oi-l) (rfl))
          (let ((ih (sml-pair-cond-unpack! x prev cond2)))
            (fact 'msg-rank-component 'T c i)
            (dk-each-leaf! (lambda () (ai ih))
              (lambda ()
                (oi-r)
                (if (dk-asm? `(= ,x ,prev))
                    (begin (subst `(= ,x ,prev)) (ass))
                    (let* ((rx (sml-rank! 'T x)) (rp (sml-rank! 'T prev)) (rc (sml-rank! 'T c)))
                      (dk-nn! `(<= (succ ,rx) ,rp) `(<= (succ ,rp) ,rc))))))))))
  (dk-ass!))
(qed 'subterm-rank)

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T a b) (IMPLIES (IS-SUBTERM T b a) (= a b)))))))))
(dk-peel!)
(fact 'subterm-in-msgs 'T 'a 'b)
(dk-split-all!)
(let* ((o1 (dk-cite! 'subterm-rank 'T 'a 'b))
      (o2 (dk-cite! 'subterm-rank 'T 'b 'a)))
  (dk-each-leaf! (lambda () (ai o1))
    (lambda ()
      (if (dk-asm? '(= a b))
          (ass)
          (dk-each-leaf! (lambda () (ai o2))
            (lambda ()
              (if (dk-asm? '(= b a))
                  (dk-have! '(= a b) (lambda () (subst '(= a b)) (rfl)))
                  (let* ((ra (sml-rank! 'T 'a)) (rb (sml-rank! 'T 'b)))
                    (dk-have! '(< 0 0)
                      (lambda () (dk-nn! `(<= (succ ,ra) ,rb) `(<= (succ ,rb) ,ra))))
                    (fact 'rr-zero-in)
                    (ai (dk-cite! 'rr-lt-irrefl 0))))))))))
(qed 'subterm-antisym)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing))
          '(pair-self-member pair-self-eq msg-set-unfold subterm-rel-unfold pair-in-cartesian-parts))
(for-each (lambda (n) (topic! n 'constructions))
          '(msg-stage-token msg-stage-keep msg-stage-list msg-stage-zero-elim msg-stage-succ-cases
            msg-stage-add msg-set-intro msg-set-elim token-in-msgs msg-stage-set msg-set-is-set
            msg-lists-are-lists list-in-some-stage list-in-msgs token-set-is-set token-not-list
            msg-induction msg-cases msg-cases-disjoint subterm-in-msgs subterm-least subterm-refl
            subterm-component subterm-cases subterm-trans subterm-of-token subterm-of-list
            token-subterm-of-list msg-rank-prop msg-stage-list-inv msg-rank-token msg-rank-component
            subterm-rank subterm-antisym))
