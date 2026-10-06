;;; strand-messages-laws.scm -- THE MESSAGES OF STRAND SPACES (the user's model, with
;;; ENCRYPTION): their laws.
;;; (~/notes/notes-60.txt item (a), the user's decision of 2026-10-06 16:40Z adding {m}_k; the
;;;  definitions are structure-library/strand-messages.scm.)
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06; ENCRYPTION added by agent S-2b the same
;;; day (S-2's key-free version: archive/2026-10-06/s2b/strand-messages-laws.scm; S-1's algebra of
;;; the paper: archive/2026-10-06/strand-messages-laws.scm, whose CAT / ENC drivers -- the tags,
;;; the ternary product, Proposition 2.12 -- are reused here).  Helper prefix: sml-.
;;;
;;; Every theorem below bills `modulo 0'.  The oracles that appear on some of them are `arith'
;;; (ground numeral facts) and `ineq' (NN linear arithmetic through dk-nn!, for the rank).
;;; Nothing is asserted, stamped or warranted.  T is the token set, K the key set; A is
;;; MSG-SET(T, K); "message" means a member of A, "list of messages" a member of TUPLES(A), and
;;; the MESSAGE such a list makes is LST(l) = [1, l]; ENCR(g, k) = [2, g, k].
;;;
;;; WHAT IS PROVEN (in this order)
;;;  0. lst-unfold, encr-unfold; FREENESS OF THE TAGS: encr-ne-list, lst-ne-encr, lst-injective,
;;;     encr-injective
;;;  1. pair-self-member, pair-self-eq            a set is the one member of PAIR(a, a)
;;;  2. msg-stage-token, -keep, -list, -encr      the stage clauses, introduction
;;;     msg-stage-zero-elim, msg-stage-succ-cases ... and elimination (three cases)
;;;     msg-stage-add                             S_j is included in S_(j + d)
;;;  3. msg-set-unfold, msg-set-intro, msg-set-elim   A is the union of the stages
;;;     token-in-msgs, cartesian3-set, msg-stage-set, msg-set-is-set
;;;     msg-lists-are-lists, list-in-some-stage, list-in-msgs (LST(l) is a message),
;;;     encr-in-msgs (ENCR(g, k) is a message), lst-in-tuples-set, encr-in-tuples-set (both
;;;     constructors make LISTS as sets -- what the token law needs)
;;;  4. token-set-is-set, token-not-list, token-ne-list, encr-ne-token   THE TOKEN LAW at work
;;;     msg-induction                             STRUCTURAL INDUCTION, class form, three clauses
;;;     msg-cases                                 a message is a token, an LST or an ENCR
;;;  5. pair-in-cartesian-parts, subterm-rel-unfold, subterm-in-msgs, subterm-least,
;;;     subterm-refl, subterm-component, subterm-encr   the clauses, minimality
;;;     subterm-cases (INVERSION, three cases), subterm-trans, subterm-of-token, subterm-of-list,
;;;     subterm-of-encr, token-subterm-of-list, token-subterm-of-encr, subterm-encr-other-key
;;;     (the paper's Proposition 2.12)
;;;  6. msg-rank-prop, msg-stage-list-inv, msg-stage-encr-inv, msg-rank-token,
;;;     msg-rank-component, msg-rank-encr, subterm-rank, subterm-antisym
;;;
;;; THE TECHNIQUE (S-1's, kept).  (a) A stage hypothesis is opened on a LANE: the claim
;;; (IN m BODY) is proved by rewriting BODY back to the stage term (there is no hypothesis-side
;;; subst).  (b) Every property of the subterm relation that is not one of its three clauses is
;;; ONE device: `subterm-least' at the separation
;;;     RR = { p in SUBTERM-REL(T, K) : exists u, v. p = [u, v] and COND(u, v) },
;;; shown to be in POWER(A x A) (a set, as T and K are) and closed under the three clauses; then
;;; every subterm pair satisfies COND.  `sml-closed-pairs!' reduces each closure obligation to the
;;; one fact the new pair needs.  (c) The rank is an IOTA: `iota-d' with existence from
;;; nn-least-element over the stage indices holding m, uniqueness from nn-le-antisym.
;;;
;;; THE KEY IS NOT A SUBTERM.  Clause (iii) of IS-SUBTERM-CLOSED puts below ENCR(g, k) only the
;;; subterms of g; `token-subterm-of-encr' (a token below an encryption is below its plaintext)
;;; is the form the adversary bound cites.  The convention is the paper's (Definition 2.11) and is
;;; on the report as a decision for the user to confirm.
;;;
;;; TYPE BEFORE YOU INSTANTIATE: a predicate hypothesis IS-SUBTERM(T, K, a, NTH(i, l)) does not
;;; certify NTH(i, l) as defined, so every component is typed by `nth-in-range', and every LST /
;;; ENCR term by list-in-msgs / encr-in-msgs, before anything is instantiated at it.
;;;
;;; LOAD WINDOW: after theorem-library/tuples-induction, theorem-library/matof-in-mat
;;; (tuples-mono), theorem-library/nn-least-element (the latest citation), pair-tuple-sethood,
;;; nn-order-proof, nn-order-ord, rr-order-basics; structure-library/strand-messages before it.
;;; The present slot (load.scm, after integral-laws) satisfies all of them.

;;; -----------------------------------------------------------------------
;;; helpers (prefix sml-)

(define (sml-keep-prop! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply dk-only! fs)
    (if (not (sequent-node-grounded? node)) (prop))))

;; (= L1 L2) in context, L1 and L2 literal lists whose first entries are two DIFFERENT
;; numerals: close the FALSITY goal (S-1's driver).
(define (sml-tag-absurd! l1 l2)
  (let ((t1 (cadr l1)) (t2 (cadr l2)))
    (dk-have! `(= (NTH 1 ,l2) ,t2) (lambda () (nth-r) (rfl)))
    (dk-have! `(= ,t1 (NTH 1 ,l2)) (lambda () (subst `(= ,l2 ,l1)) (nth-r) (rfl)))
    (dk-have! `(= ,t1 ,t2) (lambda () (subst `(= ,t2 (NTH 1 ,l2))) (ass)))
    (dk-have! `(NOT (= ,t1 ,t2)) (lambda () (arith)))
    (ai `(NOT (= ,t1 ,t2)))))

;; (= L1 L2) in context, literal lists of one length; the goal (= x y) with x the I-th entry
;; of L1 and y the I-th entry of L2.
(define (sml-component! l1 l2 i)
  (let* ((x (list-ref l1 i)) (y (list-ref l2 i)))
    (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
    (subst `(= ,y (NTH ,i ,l2)))
    (subst `(= ,l2 ,l1))
    (nth-r)
    (rfl)))

(define (sml-components! l1 l2)
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (let* ((g (dk-goal))
             (i (let loop ((k 1))
                  (cond ((> k (- (length l1) 1)) (error "sml-components!: no index for" g))
                        ((and (equal? (list-ref l1 k) (cadr g))
                              (equal? (list-ref l2 k) (caddr g))) k)
                        (#t (loop (+ k 1)))))))
        (sml-component! l1 l2 i)))))

;; (IN n SET) for a numeral tag n, through n in NN.
(define (sml-num-set! n)
  (dk-have! `(IN ,n SET)
    (lambda ()
      (dk-have! `(IN ,n NN) (lambda () (arith)))
      (fact 'membership-implies-sethood n 'NN)
      (ass))))

;; Skolemise the FORSOME EX in context and every FORSOME that lands from it, outermost first;
;; returns the eigenvariables in order.  A tag membership (IN v (PAIR n n)) that lands is turned
;; into (= v n) at once.
(define (sml-unpack! ex)
  (let loop ((ex ex) (acc '()))
    (let* ((before (dk-asms))
           (v (dk-skolem! ex))
           (new (filter (lambda (f) (not (member f before))) (dk-asms)))
           (tag (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) v)
                                             (dk-head-is? (caddr f) 'PAIR)))
                            new))
           (next (find-first (lambda (f) (dk-head-is? f 'FORSOME)) new)))
      (if tag
          (let ((n (cadr (caddr tag))))
            (sml-num-set! n)
            (fact 'pair-self-eq n v)))
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

;; An OR in context, split to its leaves (right-nested): HANDLER is called on each leaf with
;; the disjunct that landed there.
(define (sml-or-each! o handler)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((dk-head-is? (caddr o) 'OR) (sml-or-each! (caddr o) handler))
            (#t (handler (caddr o)))))))

;; Close the focus goal (IN x C), x a term and C built from UNION, CARTESIAN and PAIR(n, n)
;; around classes x's pieces are typed in, in context (S-1's driver).
(define (sml-fits? x c)
  (cond ((dk-asm? `(IN ,x ,c)) #t)
        ((and (pair? c) (eq? (car c) 'PAIR)) (equal? x (cadr c)))
        ((and (pair? c) (eq? (car c) 'UNION)) (or (sml-fits? x (cadr c)) (sml-fits? x (caddr c))))
        ((and (pair? c) (eq? (car c) 'CARTESIAN) (pair? x) (eq? (car x) 'LIST)
              (= (length x) (length c)))
         (let loop ((xs (cdr x)) (cs (cdr c)))
           (or (null? xs) (and (sml-fits? (car xs) (car cs)) (loop (cdr xs) (cdr cs))))))
        (#t #f)))

(define (sml-close-in!)
  (let* ((g (dk-goal)) (x (cadr g)) (c (caddr g)))
    (cond
      ((dk-asm? g) (ass))
      ((and (pair? c) (eq? (car c) 'PAIR))
       (sml-num-set! x)
       (fact 'pair-self-member x)
       (ass))
      ((and (pair? c) (eq? (car c) 'UNION))
       (let ((left? (sml-fits? x (cadr c))))
         (if (not (or left? (sml-fits? x (caddr c))))
             (error "sml-close-in!: neither side of the union fits" (expression->string g)))
         (dk-have! `(IN ,x ,(if left? (cadr c) (caddr c))) (lambda () (sml-close-in!)))
         (fact 'union-membership (cadr c) (caddr c) x)
         (sml-keep-prop! (iff-for g) `(IN ,x ,(if left? (cadr c) (caddr c))))))
      ((and (pair? c) (eq? (car c) 'CARTESIAN))
       (mac 'cartesian-decompose)
       (let loop ((xs (cdr x)))
         (if (null? xs)
             (rfl)
             (begin
               (ew (car xs))
               (dk-each-leaf! (lambda () (di))
                 (lambda ()
                   (if (dk-head-is? (dk-goal) 'FORSOME) (loop (cdr xs))
                       (if (dk-head-is? (dk-goal) '=) (rfl) (sml-close-in!)))))))))
      (#t (error "sml-close-in!: no route" (expression->string g))))))

;; The goal (= m X), X built by LST / ENCR: unfold them, replace m by the literal list the
;; context equates it with, the tag variables by their numerals (S-1's driver).
(define (sml-eq-close!)
  (for-each (lambda (f) (if (dk-contains? (dk-goal) f) (mac f))) '(LST ENCR))
  (if (equal? (cadr (dk-goal)) (caddr (dk-goal)))
      (rfl)
      (let* ((g (dk-goal)) (m (cadr g))
             (meq (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) m)
                                               (dk-head-is? (caddr f) 'LIST)))
                              (dk-asms))))
        (if (not meq) (error "sml-eq-close!: no list equation for" m))
        (subst meq)
        (let ((tagv (cadr (caddr meq))))
          (if (symbol? tagv)
              (subst (or (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) tagv)
                                                      (number? (caddr f))))
                                     (dk-asms))
                         (error "sml-eq-close!: no tag equation for" tagv)))))
        (rfl))))

;; Close an existential goal FORSOME x1 (AND (IN x1 C1) (FORSOME x2 ... (= m X))) with the
;; witnesses WS: memberships by sml-close-in!, the equation by sml-eq-close!.
(define (sml-ex-close! ws)
  (if (null? ws)
      (sml-eq-close!)
      (begin
        (ew (car ws))
        (dk-each-leaf! (lambda () (di))
          (lambda ()
            (cond ((dk-head-is? (dk-goal) 'FORSOME) (sml-ex-close! (cdr ws)))
                  ((dk-head-is? (dk-goal) '=) (sml-eq-close!))
                  (#t (sml-close-in!))))))))

;; Close a goal FORSOME x1 ... (AND ...) with the witnesses WS: each conjunct by `rfl' (an
;; equation) or from the context.
(define (sml-ex-fill! ws)
  (ew (car ws))
  (dk-conj-close!
    (lambda ()
      (cond ((dk-head-is? (dk-goal) 'FORSOME) (sml-ex-fill! (cdr ws)))
            ((dk-asm? (dk-goal)) (ass))
            ((dk-head-is? (dk-goal) '=) (rfl))
            (#t (ass))))))

;; The stage equation at n (n = 0, or (succ j) with j in NN in context), landed and returned.
(define (sml-stage-eq tt kk n)
  (if (equal? n 0)
      (dk-cite! 'msg-stage-zero tt kk)
      (dk-cite! 'msg-stage-succ tt kk (cadr n))))

;; (IN m (MSG-STAGE tt kk n)) in context: land and return (IN m BODY), BODY the right-hand side
;; of the stage equation.
(define (sml-stage-open! m tt kk n)
  (let* ((eqn (sml-stage-eq tt kk n))
         (body (caddr eqn))
         (claim `(IN ,m ,body)))
    (dk-have! claim (lambda () (subst `(= ,body (MSG-STAGE ,tt ,kk ,n))) (ass)))
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

;; (IN x SET) from (IN x C) in context.
(define (sml-set-of! x c)
  (if (not (dk-asm? `(IN ,x SET))) (fact 'membership-implies-sethood x c))
  `(IN ,x SET))

;;; -----------------------------------------------------------------------
;;; 0. The constructors as citable equations, and the freeness of the tags.

(sp (make-wff '(FORALL l (== (LST l) (LIST 1 l)))))
(di) (mac 'LST) (qrfl)
(qed 'lst-unfold)

(sp (make-wff '(FORALL g (FORALL y (== (ENCR g y) (LIST 2 g y))))))
(di) (mac 'ENCR) (qrfl)
(qed 'encr-unfold)

(sp (make-wff '(FORALL g (FORALL y (FORALL l (NOT (= (ENCR g y) (LST l))))))))
(di) (mac 'ENCR) (mac 'LST) (di)
(sml-tag-absurd! '(LIST 2 g y) '(LIST 1 l))
(qed 'encr-ne-list)

(sp (make-wff '(FORALL l (FORALL g (FORALL y (NOT (= (LST l) (ENCR g y))))))))
(di) (mac 'ENCR) (mac 'LST) (di)
(sml-tag-absurd! '(LIST 1 l) '(LIST 2 g y))
(qed 'lst-ne-encr)

(sp (make-wff '(FORALL l (FORALL l2 (IMPLIES (= (LST l) (LST l2)) (= l l2))))))
(di) (mac 'LST) (di)
(sml-component! '(LIST 1 l) '(LIST 1 l2) 2)
(qed 'lst-injective)

(sp (make-wff '(FORALL g (FORALL y (FORALL u (FORALL z
   (IMPLIES (= (ENCR g y) (ENCR u z)) (AND (= g u) (= y z)))))))))
(di) (mac 'ENCR) (di)
(sml-components! '(LIST 2 g y) '(LIST 2 u z))
(qed 'encr-injective)

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

(sp (make-wff '(FORALL T (FORALL K (FORALL tk (IMPLIES (IN tk T) (IN tk (MSG-STAGE T K 0))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K 0))
(ass)
(qed 'msg-stage-token)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T K n)) (IN m (MSG-STAGE T K (succ n)))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(sml-close-in!)
(qed 'msg-stage-keep)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL l
   (IMPLIES (IN n NN) (IMPLIES (IN l (TUPLES (MSG-STAGE T K n)))
     (IN (LST l) (MSG-STAGE T K (succ n)))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(mac 'LST)
(sml-close-in!)
(qed 'msg-stage-list)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL g (FORALL y
   (IMPLIES (IN n NN) (IMPLIES (IN g (MSG-STAGE T K n)) (IMPLIES (IN y K)
      (IN (ENCR g y) (MSG-STAGE T K (succ n)))))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(mac 'ENCR)
(sml-close-in!)
(qed 'msg-stage-encr)

(sp (make-wff '(FORALL T (FORALL K (FORALL m (IMPLIES (IN m (MSG-STAGE T K 0)) (IN m T)))))))
(dk-peel!)
(sml-stage-open! 'm 'T 'K 0)
(qed 'msg-stage-zero-elim)

(define sml-sn '(MSG-STAGE T K n))
(define sml-c1 '(CARTESIAN (PAIR 1 1) (TUPLES (MSG-STAGE T K n))))
(define sml-c2 '(CARTESIAN (PAIR 2 2) (MSG-STAGE T K n) K))

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T K (succ n)))
     (OR (IN m (MSG-STAGE T K n))
         (OR (FORSOME l (AND (IN l (TUPLES (MSG-STAGE T K n))) (= m (LST l))))
             (FORSOME g (AND (IN g (MSG-STAGE T K n))
                             (FORSOME y (AND (IN y K) (= m (ENCR g y))))))))))))))))
(dk-peel!)
(let ((o1 (sml-union-open! (sml-stage-open! 'm 'T 'K '(succ n)))))
  (dk-each-leaf! (lambda () (ai o1))
    (lambda ()
      (if (dk-asm? `(IN m ,sml-sn))
          (begin (oi-l) (ass))
          (let ((o2 (sml-union-open! `(IN m (UNION ,sml-c1 ,sml-c2)))))
            (dk-each-leaf! (lambda () (ai o2))
              (lambda ()
                (oi-r)
                (let ((c (if (dk-asm? `(IN m ,sml-c1)) sml-c1 sml-c2)))
                  (if (eq? c sml-c1) (oi-l) (oi-r))
                  (sml-ex-close! (cdr (sml-unpack! (sml-cart-open! `(IN m ,c)))))))))))))
(qed 'msg-stage-succ-cases)

;;; S_j is included in S_(j + d).  The induction variable d is OUTERMOST, as `ni' needs it.
(sp (make-wff '(FORALL d (IMPLIES (IN d NN)
   (FORALL T (FORALL K (FORALL j (FORALL m
     (IMPLIES (IN j NN) (IMPLIES (IN m (MSG-STAGE T K j)) (IN m (MSG-STAGE T K (+ j d)))))))))))))
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
       (g (dk-goal))                          ; (IN m (MSG-STAGE T K (+ j (succ n))))
       (m (cadr g)) (stage (caddr g))
       (tt (cadr stage)) (kk (caddr stage)) (sum (cadddr stage))
       (j (cadr sum)) (n (cadr (caddr sum))))
  (subst (dk-cite! 'nn-add-succ j n))
  (dk-have! `(AND (IN ,j NN) (IN ,n NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'nn-add-closed j n)
  (dk-apply! ih tt kk j m)
  (fact 'msg-stage-keep tt kk `(+ ,j ,n) m)
  (ass))
(qed 'msg-stage-add)

;;; -----------------------------------------------------------------------
;;; 3. The message set.

(sp (make-wff '(FORALL T (FORALL K (== (MSG-SET T K) (BIG-UNION n NN (MSG-STAGE T K n)))))))
(di) (mac 'MSG-SET) (qrfl)
(qed 'msg-set-unfold)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T K n)) (IN m (MSG-SET T K))))))))))
(dk-peel!)
(mac 'MSG-SET)
(dk-each-leaf! (lambda () (bu-mi 'n)) (lambda () (ass)))
(qed 'msg-set-intro)

(sp (make-wff '(FORALL T (FORALL K (FORALL m
   (IMPLIES (IN m (MSG-SET T K)) (FORSOME n (AND (IN n NN) (IN m (MSG-STAGE T K n))))))))))
(dk-peel!)
(let* ((eqn (dk-cite! 'msg-set-unfold 'T 'K))
       (bu `(IN m ,(caddr eqn))))
  (dk-have! bu (lambda () (subst `(= ,(caddr eqn) (MSG-SET T K))) (ass)))
  (let ((before (dk-asms)))
    (bu-me bu)
    (let ((typ (find-first (lambda (f) (and (not (member f before)) (dk-head-is? f 'IN)
                                            (eq? (caddr f) 'NN)))
                           (dk-asms))))
      (ew (cadr typ))
      (dk-conj-close! (lambda () (ass))))))
(qed 'msg-set-elim)

;; (IN x (MSG-SET tt kk)) in context: land a stage index and the stage membership; return it.
(define (sml-set-open! x tt kk)
  (dk-skolem! (dk-cite! 'msg-set-elim tt kk x)))

(sp (make-wff '(FORALL T (FORALL K (FORALL tk (IMPLIES (IN tk T) (IN tk (MSG-SET T K))))))))
(dk-peel!)
(fact 'msg-stage-token 'T 'K 'tk)
(fact 'nn-zero-in)
(fact 'msg-set-intro 'T 'K 0 'tk)
(ass)
(qed 'token-in-msgs)

;; (IN t SET) for t built from symbols / stages with a sethood in context, numeral singletons
;; PAIR(n, n), UNION, TUPLES and CARTESIAN (binary or ternary).
(define (sml-set! t)
  (let ((goal `(IN ,t SET)))
    (cond
      ((dk-asm? goal) goal)
      ((and (pair? t) (eq? (car t) 'PAIR))
       (sml-num-set! (cadr t))
       (dk-have! `(AND (IN ,(cadr t) SET) (IN ,(caddr t) SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
       (fact 'pairing (cadr t) (caddr t))
       goal)
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
      ((and (pair? t) (eq? (car t) 'CARTESIAN) (= (length t) 4))
       (for-each sml-set! (cdr t))
       (fact 'cartesian3-set (cadr t) (caddr t) (cadddr t))
       goal)
      (#t (error "sml-set!: no route to the sethood of" (expression->string t))))))

(define (sml-set-close!)
  (let ((g (dk-goal)))
    (sml-set! (cadr g))
    (if (and (alpha-equiv? (dk-goal) g) (dk-asm? g)) (ass))))

;;; The ternary product is a set by REPLACEMENT over the binary product U x (V x W) (S-1).
(define sml-phi
  '(VNB-LAMBDA cqp_ (CARTESIAN U (CARTESIAN V W))
     (LIST (NTH 1 cqp_) (NTH 1 (NTH 2 cqp_)) (NTH 2 (NTH 2 cqp_)))))

(sp (make-wff '(FORALL U (FORALL V (FORALL W
   (IMPLIES (IN U SET) (IMPLIES (IN V SET) (IMPLIES (IN W SET) (IN (CARTESIAN U V W) SET)))))))))
(dk-peel!)
(let* ((ww '(CARTESIAN U (CARTESIAN V W)))
       (img `(IMAGE ,sml-phi ,ww))
       (sub `(SUBSET (CARTESIAN U V W) ,img)))
  (sml-set! ww)
  (fact 'image-set sml-phi ww)
  (dk-have! sub
    (lambda ()
      (mac 'subset-def)
      (di)
      (let* ((x (cadr (dk-goal)))
             (vs (sml-unpack! (sml-cart-open! `(IN ,x (CARTESIAN U V W)))))
             (a1 (car vs)) (a2 (cadr vs)) (a3 (caddr vs))
             (pr `(LIST ,a1 (LIST ,a2 ,a3))))
        (dk-image-goal!)
        (ew pr)
        (fact 'pair-in-cartesian 'V 'W a2 a3)
        (fact 'pair-in-cartesian 'U '(CARTESIAN V W) a1 `(LIST ,a2 ,a3))
        (dk-each-leaf! (lambda () (di))
          (lambda ()
            (if (dk-head-is? (dk-goal) 'IN)
                (ass)
                (begin
                  (dk-lam-b!)
                  (let loop () (if (dk-contains? (dk-goal) 'NTH) (begin (nth-r) (loop))))
                  (subst (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) x))) (dk-asms)))
                  (rfl))))))))
  (fact 'subclass-of-set-is-set '(CARTESIAN U V W) img)
  (ass))
(qed 'cartesian3-set)

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET) (IN (MSG-STAGE T K n) SET)))))))))
(define sml-cases2 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases2))
(dk-peel!)
(subst (sml-stage-eq 'T 'K 0))
(ass)
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases2))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (stage (cadr (dk-goal)))
       (tt (cadr stage)) (kk (caddr stage)) (n (cadr (cadddr stage))))
  (dk-apply! ih tt kk)
  (subst (sml-stage-eq tt kk `(succ ,n)))
  (sml-set-close!))
(qed 'msg-stage-set)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET) (IN (MSG-SET T K) SET)))))))
(dk-peel!)
(mac 'MSG-SET)
(dk-each-leaf! (lambda () (bu-set))
  (lambda ()
    (if (dk-head-is? (dk-goal) 'IN)
        (begin (fact 'nn-is-set) (ass))
        (begin (dk-peel!)
               (fact 'msg-stage-set (cadddr (cadr (dk-goal))) 'T 'K)
               (ass)))))
(qed 'msg-set-is-set)

;; "C1 inside C2" as the universal tuples-mono wants, proved by THUNK on the peeled leaf.
(define (sml-incl! c1 c2 thunk)
  (let ((incl `(FORALL smw_ (IMPLIES (IN smw_ ,c1) (IN smw_ ,c2)))))
    (dk-have! incl (lambda () (dk-peel!) (thunk (cadr (dk-goal)))))
    incl))

(define (sml-tuples-lift! l c1 c2 thunk)
  (sml-incl! c1 c2 thunk)
  (dk-apply! (dk-cite! 'tuples-mono c1 c2) l))

(sp (make-wff '(FORALL T (FORALL K (FORALL l
   (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IN l (TUPLES SET))))))))
(dk-peel!)
(sml-tuples-lift! 'l '(MSG-SET T K) 'SET
  (lambda (w) (fact 'membership-implies-sethood w '(MSG-SET T K)) (ass)))
(ass)
(qed 'msg-lists-are-lists)

;;; A list of messages has all its components in ONE stage (S-2's list induction).
(define sml-lis-class
  '(SEP smy_ (TUPLES (MSG-SET T K))
        (FORSOME smst_ (AND (IN smst_ NN) (IN smy_ (TUPLES (MSG-STAGE T K smst_)))))))

(sp (make-wff '(FORALL T (FORALL K (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T K)))
   (FORSOME n (AND (IN n NN) (IN l (TUPLES (MSG-STAGE T K n)))))))))))
(dk-peel!)
(let* ((ind0 (lookup-theorem 'tuples-induction))
       (ind (subst-free (quantifier-var (quantifier-body ind0)) sml-lis-class
              (quantifier-body (subst-free (quantifier-var ind0) '(MSG-SET T K) (quantifier-body ind0)))))
       (prem (cadr ind))
       (h-base (cadr prem))
       (h-step (caddr prem)))
  (dk-have! h-base
    (lambda ()
      (in-sep! (lambda () (fact 'empty-in-tuples '(MSG-SET T K)) (ass))
               (lambda ()
                 (ew 0)
                 (dk-conj-close!
                   (lambda ()
                     (if (equal? (cadr (dk-goal)) 0)
                         (begin (fact 'nn-zero-in) (ass))
                         (begin (subst (sml-stage-eq 'T 'K 0))
                                (fact 'empty-in-tuples 'T)
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
             (i (sml-set-open! x 'T 'K))
             (sij `(MSG-STAGE T K (+ ,i ,j))))
        (dk-have! `(AND (IN ,i NN) (IN ,j NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
        (fact 'nn-add-closed i j)
        (fact 'msg-stage-add j 'T 'K i x)                ; x in S_(i + j)
        (sml-tuples-lift! mm `(MSG-STAGE T K ,j) sij
          (lambda (w)
            (fact 'msg-stage-add i 'T 'K j w)             ; w in S_(j + i)
            (fact 'nn-add-comm i j)
            (subst `(= (+ ,i ,j) (+ ,j ,i)))
            (ass)))
        (dk-have! `(AND (IN ,x ,sij) (IN ,mm (TUPLES ,sij))) (lambda () (dk-conj-close! (lambda () (ass)))))
        (fact 'cons-in-tuples sij x mm)
        (in-sep! (lambda ()
                   (dk-have! `(AND (IN ,x (MSG-SET T K)) (IN ,mm (TUPLES (MSG-SET T K))))
                     (lambda () (dk-conj-close! (lambda () (ass)))))
                   (fact 'cons-in-tuples '(MSG-SET T K) x mm)
                   (ass))
                 (lambda ()
                   (ew `(+ ,i ,j))
                   (dk-conj-close! (lambda () (ass))))))))
  (dk-have! prem (lambda () (dk-conj-close! (lambda () (ass)))))
  (let ((all (dk-cite! 'tuples-induction '(MSG-SET T K) sml-lis-class)))
    (dk-apply! all 'l)
    (sep-me `(IN l ,sml-lis-class))
    (ass)))
(qed 'list-in-some-stage)

(sp (make-wff '(FORALL T (FORALL K (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IN (LST l) (MSG-SET T K))))))))
(dk-peel!)
(let ((n (dk-skolem! (dk-cite! 'list-in-some-stage 'T 'K 'l))))
  (fact 'msg-stage-list 'T 'K n 'l)
  (fact 'nn-succ-closed n)
  (fact 'msg-set-intro 'T 'K `(succ ,n) '(LST l))
  (ass))
(qed 'list-in-msgs)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (FORALL y
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K) (IN (ENCR g y) (MSG-SET T K))))))))))
(dk-peel!)
(let ((i (sml-set-open! 'g 'T 'K)))
  (fact 'msg-stage-encr 'T 'K i 'g 'y)
  (fact 'nn-succ-closed i)
  (fact 'msg-set-intro 'T 'K `(succ ,i) '(ENCR g y))
  (ass))
(qed 'encr-in-msgs)

;;; Both constructors make LISTS (members of TUPLES(SET)) -- what the token law separates from.
(define (sml-ti-close!)
  (dk-each-leaf! (lambda () (ti))
    (lambda () (if (number? (cadr (dk-goal))) (sml-num-set! (cadr (dk-goal))) (ass)))))

(sp (make-wff '(FORALL l (IMPLIES (IN l SET) (IN (LST l) (TUPLES SET))))))
(dk-peel!)
(mac 'LST)
(sml-ti-close!)
(qed 'lst-in-tuples-set)

(sp (make-wff '(FORALL g (FORALL y (IMPLIES (IN g SET) (IMPLIES (IN y SET) (IN (ENCR g y) (TUPLES SET))))))))
(dk-peel!)
(mac 'ENCR)
(sml-ti-close!)
(qed 'encr-in-tuples-set)

;;; -----------------------------------------------------------------------
;;; 4. The token law, structural induction, the three cases.

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

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T)
   (FORALL tk (IMPLIES (IN tk T) (NOT (IN tk (TUPLES (MSG-SET T K)))))))))))
(dk-peel!)
(let ((nl (sml-token-law! 'T 'tk)))
  (di)
  (fact 'msg-lists-are-lists 'T 'K 'tk)
  (ai nl))
(qed 'token-not-list)

;;; A token is no LIST message and no ENCRYPTION (the token law: both are lists as sets).
(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
   (FORALL tk (FORALL l (IMPLIES (IN tk T) (IMPLIES (IN l SET) (NOT (= tk (LST l)))))))))))
(dk-peel!)
(di)
(let ((nl (sml-token-law! 'T 'tk)))
  (fact 'lst-in-tuples-set 'l)
  (dk-have! '(IN tk (TUPLES SET)) (lambda () (subst '(= tk (LST l))) (ass)))
  (ai nl))
(qed 'token-ne-list)

(sp (make-wff '(FORALL T (IMPLIES (IS-TOKEN-SET T)
   (FORALL tk (FORALL g (FORALL y (IMPLIES (IN tk T) (IMPLIES (IN g SET) (IMPLIES (IN y SET)
     (NOT (= tk (ENCR g y)))))))))))))
(dk-peel!)
(di)
(let ((nl (sml-token-law! 'T 'tk)))
  (fact 'encr-in-tuples-set 'g 'y)
  (dk-have! '(IN tk (TUPLES SET)) (lambda () (subst '(= tk (ENCR g y))) (ass)))
  (ai nl))
(qed 'encr-ne-token)

;; The three hypotheses of msg-induction at the class CC (read off the theorem).
(define (sml-ind-hyps tt kk cc)
  (let* ((th (lookup-theorem 'msg-induction))
         (b1 (subst-free (quantifier-var th) tt (quantifier-body th)))
         (b2 (subst-free (quantifier-var b1) kk (quantifier-body b1)))
         (b3 (subst-free (quantifier-var b2) cc (quantifier-body b2))))
    (list (cadr b3) (cadr (caddr b3)) (cadr (caddr (caddr b3))))))

(sp (make-wff '(FORALL T (FORALL K (FORALL C
   (IMPLIES (FORALL tk (IMPLIES (IN tk T) (IN tk C)))
   (IMPLIES (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T K)))
              (IMPLIES (FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
                                    (IN (NTH i l) C)))))
                       (IN (LST l) C))))
   (IMPLIES (FORALL g (FORALL y (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
              (IMPLIES (IN g C) (IN (ENCR g y) C))))))
     (FORALL m (IMPLIES (IN m (MSG-SET T K)) (IN m C)))))))))))
(let* ((landed (dk-peel!))
       (g0 (dk-goal)) (m0 (cadr g0)) (cc (caddr g0)) (tt 'T) (kk 'K)
       (h-tok (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (not (dk-contains? f 'LST))
                                               (not (dk-contains? f 'ENCR)))) landed)
                  (error "msg-induction: no token hypothesis")))
       (h-list (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'LST))) landed)
                   (error "msg-induction: no list hypothesis")))
       (h-encr (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'ENCR))) landed)
                   (error "msg-induction: no encryption hypothesis")))
       (claim `(FORALL smn_ (IMPLIES (IN smn_ NN)
                 (FORALL smm_ (IMPLIES (IN smm_ (MSG-STAGE ,tt ,kk smn_)) (IN smm_ ,cc)))))))
  (dk-have! claim
    (lambda ()
      (let ((cases (dk-opened (lambda () (ni)))))
        ;; base: a member of stage 0 is a token
        (dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) cases))
        (dk-peel!)
        (let ((m (cadr (dk-goal))))
          (fact 'msg-stage-zero-elim tt kk m)
          (dk-apply! h-tok m)
          (ass))
        ;; step: a member of stage succ n is kept, an LST of stage-n messages, or an ENCR
        (dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) cases))
        (let* ((landed (dk-peel!))
               (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
               (m (cadr (dk-goal)))
               (n (cadr (cadddr (caddr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) m)))
                                                   landed)))))
               (sn `(MSG-STAGE ,tt ,kk ,n))
               (o (dk-cite! 'msg-stage-succ-cases tt kk n m)))
          (sml-or-each! o
            (lambda (d)
              (cond
                ((dk-head-is? d 'IN) (dk-apply! ih m) (ass))
                ((dk-head-is? (caddr (cadr (caddr d))) 'TUPLES)
                 (let* ((l (car (sml-unpack! d)))
                        (comps `(FORALL smi_ (IMPLIES (IN smi_ NN) (IMPLIES (<= 1 smi_)
                                   (IMPLIES (<= smi_ (LENGTH ,l)) (IN (NTH smi_ ,l) ,cc)))))))
                   (sml-tuples-lift! l sn `(MSG-SET ,tt ,kk)
                     (lambda (w) (fact 'msg-set-intro tt kk n w) (ass)))
                   (dk-have! comps
                     (lambda ()
                       (dk-peel!)
                       (let ((i (cadr (cadr (dk-goal)))))
                         (sml-nth-in! sn i l)
                         (dk-apply! ih `(NTH ,i ,l))
                         (ass))))
                   (dk-apply! h-list l)
                   (subst `(= ,m (LST ,l)))
                   (ass)))
                (#t
                 (let* ((vs (sml-unpack! d)) (g (car vs)) (y (cadr vs)))
                   (fact 'msg-set-intro tt kk n g)
                   (dk-apply! ih g)
                   (dk-apply! h-encr g y)
                   (subst `(= ,m (ENCR ,g ,y)))
                   (ass))))))))))
  ;; the message is in some stage, and the claim holds there
  (let ((n (sml-set-open! m0 tt kk)))
    (dk-apply! claim n m0)
    (ass)))
(qed 'msg-induction)

(sp (make-wff '(FORALL T (FORALL K (FORALL m (IMPLIES (IN m (MSG-SET T K))
   (OR (IN m T)
       (OR (FORSOME l (AND (IN l (TUPLES (MSG-SET T K))) (= m (LST l))))
           (FORSOME g (AND (IN g (MSG-SET T K)) (FORSOME y (AND (IN y K) (= m (ENCR g y))))))))))))))
(dk-peel!)
(let* ((cc '(SEP smz_ (MSG-SET T K)
              (OR (IN smz_ T)
                  (OR (FORSOME sml2_ (AND (IN sml2_ (TUPLES (MSG-SET T K))) (= smz_ (LST sml2_))))
                      (FORSOME smg2_ (AND (IN smg2_ (MSG-SET T K))
                                          (FORSOME smy2_ (AND (IN smy2_ K) (= smz_ (ENCR smg2_ smy2_))))))))))
       (hs (sml-ind-hyps 'T 'K cc)))
  (dk-have! (car hs)
    (lambda ()
      (dk-peel!)
      (let ((x (cadr (dk-goal))))
        (in-sep! (lambda () (fact 'token-in-msgs 'T 'K x) (ass))
                 (lambda () (oi-l) (ass))))))
  (dk-have! (cadr hs)
    (lambda ()
      (dk-peel!)
      (let* ((x (cadr (dk-goal))) (l (cadr x)))
        (fact 'list-in-msgs 'T 'K l)
        (in-sep! (lambda () (ass))
                 (lambda () (oi-r) (oi-l) (sml-ex-fill! (list l)))))))
  (dk-have! (caddr hs)
    (lambda ()
      (dk-peel!)
      (let* ((x (cadr (dk-goal))) (g (cadr x)) (y (caddr x)))
        (fact 'encr-in-msgs 'T 'K g y)
        (in-sep! (lambda () (ass))
                 (lambda () (oi-r) (oi-r) (sml-ex-fill! (list g y)))))))
  (dk-apply! (dk-cite! 'msg-induction 'T 'K cc) 'm)
  (sep-me `(IN m ,cc))
  (dk-ass!))
(qed 'msg-cases)

;;; -----------------------------------------------------------------------
;;; 5. The subterm relation: its three clauses, minimality, inversion.

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

(sp (make-wff '(FORALL T (FORALL K (== (SUBTERM-REL T K)
   (SEP p_ (CARTESIAN (MSG-SET T K) (MSG-SET T K))
        (FORALL q_ (IMPLIES (IN q_ (POWER (CARTESIAN (MSG-SET T K) (MSG-SET T K))))
                            (IMPLIES (IS-SUBTERM-CLOSED T K q_) (IN p_ q_))))))))))
(di) (mac 'SUBTERM-REL) (qrfl)
(qed 'subterm-rel-unfold)

(define (sml-msgs tt kk) `(MSG-SET ,tt ,kk))
(define (sml-box tt kk) `(CARTESIAN (MSG-SET ,tt ,kk) (MSG-SET ,tt ,kk)))

;; (IS-SUBTERM tt kk a b) in context: land (IN a A), (IN b A) and the universal "every closed q
;; in POWER(A x A) holds [a, b]", which is returned.
(define (sml-st-open! tt kk a b)
  (let* ((hyp `(IS-SUBTERM ,tt ,kk ,a ,b))
         (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt ,kk)))
         (eqn (dk-cite! 'subterm-rel-unfold tt kk))
         (sepm `(IN (LIST ,a ,b) ,(caddr eqn))))
    (dk-have! mem (lambda () (fact 'is-subterm tt kk a b) (sml-keep-prop! (iff-for hyp) hyp)))
    (dk-have! sepm (lambda () (subst `(= ,(caddr eqn) (SUBTERM-REL ,tt ,kk))) (ass)))
    (let* ((landed (dk-landed (lambda () (sep-me sepm))))
           (univ (or (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed)
                     (error "sml-st-open!: no universal landed"))))
      (fact 'pair-in-cartesian-parts (sml-msgs tt kk) (sml-msgs tt kk) a b)
      (dk-split-all!)
      univ)))

;; The kind of a clause of IS-SUBTERM-CLOSED: reflexivity binds one variable; the list clause
;; mentions LST, the encryption clause ENCR.
(define (sml-clause-kind f)
  (let loop ((g f) (k 0))
    (cond ((dk-head-is? g 'FORALL) (loop (caddr g) (+ k 1)))
          ((dk-head-is? g 'IMPLIES) (loop (caddr g) k))
          ((< k 3) 'refl)
          ;; the consequent (IN (LIST a X) r): the head of X decides (r itself may mention both)
          ((dk-head-is? (caddr (cadr g)) 'LST) 'list)
          ((dk-head-is? (caddr (cadr g)) 'ENCR) 'encr)
          (#t (error "sml-clause-kind: no kind for" (expression->string f))))))

;; The goal (IS-SUBTERM tt kk a b) with (IN a A), (IN b A) in context.  STEP is called on the
;; lane where q is a closed relation in POWER(A x A), the three clauses split into the context,
;; as (STEP q CLAUSE-OF); it must close (IN [a, b] q).  PRE runs first with q.
(define (sml-st-intro! tt kk a b pre step)
  (mac 'is-subterm)
  (mac 'SUBTERM-REL)
  (in-sep! (lambda () (fact 'pair-in-cartesian (sml-msgs tt kk) (sml-msgs tt kk) a b) (ass))
           (lambda ()
             (dk-peel!)
             (let* ((q (caddr (dk-goal)))
                    (closed `(IS-SUBTERM-CLOSED ,tt ,kk ,q)))
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

(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL b
   (IMPLIES (IS-SUBTERM T K a b) (AND (IN a (MSG-SET T K)) (IN b (MSG-SET T K))))))))))
(dk-peel!)
(sml-st-open! 'T 'K 'a 'b)
(dk-conj-close! (lambda () (ass)))
(qed 'subterm-in-msgs)

(sp (make-wff '(FORALL T (FORALL K (FORALL r
   (IMPLIES (IN r (POWER (CARTESIAN (MSG-SET T K) (MSG-SET T K))))
   (IMPLIES (IS-SUBTERM-CLOSED T K r)
     (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b) (IN (LIST a b) r)))))))))))
(dk-peel!)
(dk-apply! (sml-st-open! 'T 'K 'a 'b) 'r)
(ass)
(qed 'subterm-least)

(sp (make-wff '(FORALL T (FORALL K (FORALL a (IMPLIES (IN a (MSG-SET T K)) (IS-SUBTERM T K a a)))))))
(dk-peel!)
(sml-st-intro! 'T 'K 'a 'a (lambda (q) #t)
  (lambda (q clause-of) (dk-apply! (clause-of 'refl) 'a) (ass)))
(qed 'subterm-refl)

;;; A subterm of a component is a subterm of the list message.
(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL l (FORALL i
   (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
     (IMPLIES (IS-SUBTERM T K a (NTH i l)) (IS-SUBTERM T K a (LST l))))))))))))))
(dk-peel!)
(sml-nth-in! '(MSG-SET T K) 'i 'l)
(fact 'list-in-msgs 'T 'K 'l)
(let ((u (sml-st-open! 'T 'K 'a '(NTH i l))))
  (sml-st-intro! 'T 'K 'a '(LST l)
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'list) 'a 'l 'i) (ass))))
(qed 'subterm-component)

;;; A subterm of the plaintext is a subterm of the encryption.
(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL g (FORALL y
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
     (IMPLIES (IS-SUBTERM T K a g) (IS-SUBTERM T K a (ENCR g y))))))))))))
(dk-peel!)
(fact 'encr-in-msgs 'T 'K 'g 'y)
(let ((u (sml-st-open! 'T 'K 'a 'g)))
  (sml-st-intro! 'T 'K 'a '(ENCR g y)
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'encr) 'a 'g 'y) (ass))))
(qed 'subterm-encr)

;;; -----------------------------------------------------------------------
;;; The one device: subterm-least at a SEP of SUBTERM-REL by a condition on the pair.

(define (sml-st-mem! tt kk a b)          ; from (IS-SUBTERM tt kk a b)
  (let ((hyp `(IS-SUBTERM ,tt ,kk ,a ,b)) (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt ,kk))))
    (dk-have! mem (lambda () (fact 'is-subterm tt kk a b) (sml-keep-prop! (iff-for hyp) hyp)))
    mem))
(define (sml-st-pred! tt kk a b)         ; from (IN (LIST a b) (SUBTERM-REL tt kk))
  (let ((hyp `(IS-SUBTERM ,tt ,kk ,a ,b)) (mem `(IN (LIST ,a ,b) (SUBTERM-REL ,tt ,kk))))
    (dk-have! hyp (lambda () (fact 'is-subterm tt kk a b) (sml-keep-prop! (iff-for hyp) mem)))
    hyp))

;; (IN (SUBTERM-REL tt kk) SET), from the sethood of T and K in context.
(define (sml-st-set! tt kk)
  (let* ((eqn (dk-cite! 'subterm-rel-unfold tt kk))
         (sepf (caddr eqn))
         (goal `(IN (SUBTERM-REL ,tt ,kk) SET)))
    (fact 'msg-set-is-set tt kk)
    (dk-have! `(IN ,sepf SET) (lambda () (dk-each-leaf! (lambda () (sep-set)) (lambda () (sml-set-close!)))))
    (dk-have! goal (lambda () (subst eqn) (ass)))
    goal))

;; The goal (IN RR (POWER (A x A))) for RR a SEP over SUBTERM-REL(tt, kk).
(define (sml-subrel-power! tt kk rr)
  (sml-st-set! tt kk)
  (mac 'power-set-membership)
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (if (dk-head-is? (dk-goal) 'IN)
          (dk-each-leaf! (lambda () (sep-set)) (lambda () (ass)))
          (let* ((landed (dk-peel!))
                 (z (cadr (dk-goal)))
                 (eqn (dk-cite! 'subterm-rel-unfold tt kk))
                 (sepf (caddr eqn)))
            (sep-me `(IN ,z ,rr))
            (dk-have! `(IN ,z ,sepf) (lambda () (subst `(= ,sepf (SUBTERM-REL ,tt ,kk))) (ass)))
            (sep-me `(IN ,z ,sepf))
            (ass))))))

(define (sml-pair-cond p cond2)          ; exists u, v. p = [u, v] and COND2(u, v)
  `(FORSOME siu_ (FORSOME siv_ (AND (= ,p (LIST siu_ siv_)) ,(cond2 'siu_ 'siv_)))))

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

;; The goal (IN [a, b] RR): the domain by IS-SUBTERM (in context), the condition by witnesses
;; a, b and COND-THUNK on COND2(a, b).
(define (sml-pair-cond-intro! tt kk a b cond-thunk)
  (sml-st-mem! tt kk a b)
  (in-sep! (lambda () (ass))
           (lambda ()
             (ew a)
             (ew b)
             (dk-each-leaf! (lambda () (di))
               (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (cond-thunk)))))))

;; The membership (IN (LIST x P) RR') in context, RR' alpha-equivalent to RR.
(define (sml-find-pair x p rr)
  (or (find-first (lambda (f) (and (dk-head-is? f 'IN) (alpha-equiv? (caddr f) rr)
                                   (dk-head-is? (cadr f) 'LIST)
                                   (equal? (cadr (cadr f)) x)
                                   (p (caddr (cadr f)))))
                  (dk-asms))
      (error "sml-find-pair: no predecessor pair" (expression->string (dk-goal)))))

;; The goal (IS-SUBTERM-CLOSED tt kk RR): unfold, and run (CLOSE KIND x b INFO) on the condition
;; leaf of each clause's new pair [x, b]: INFO is () for reflexivity, (l prev i) for the list
;; clause (b = LST(l), prev = NTH(i, l)), (g y) for the encryption clause (b = ENCR(g, y)).  On
;; that leaf IS-SUBTERM of both pairs and the typings are in context.
(define (sml-closed-pairs! tt kk rr close)
  (mac 'is-subterm-closed)
  (dk-conj-close!
    (lambda ()
      (let ((kind (sml-clause-kind (dk-goal))))
        (dk-peel!)
        (let* ((pr (cadr (dk-goal))) (x (cadr pr)) (b (caddr pr)))
          (case kind
            ((refl)
             (fact 'subterm-refl tt kk x)
             (sml-pair-cond-intro! tt kk x x (lambda () (close kind x b '()))))
            ((list)
             (let* ((l (cadr b))
                    (prevmem (sml-find-pair x (lambda (p) (and (dk-head-is? p 'NTH) (equal? (caddr p) l))) rr))
                    (prev (caddr (cadr prevmem)))
                    (i (cadr prev)))
               (sep-me prevmem)
               (sml-nth-in! (sml-msgs tt kk) i l)
               (sml-st-pred! tt kk x prev)
               (fact 'list-in-msgs tt kk l)
               (fact 'subterm-component tt kk x l i)
               (fact 'subterm-in-msgs tt kk x prev)
               (dk-split-all!)
               (sml-pair-cond-intro! tt kk x b (lambda () (close kind x b (list l prev i))))))
            ((encr)
             (let* ((g (cadr b)) (y (caddr b))
                    (prevmem (sml-find-pair x (lambda (p) (equal? p g)) rr)))
               (sep-me prevmem)
               (sml-st-pred! tt kk x g)
               (fact 'encr-in-msgs tt kk g y)
               (fact 'subterm-encr tt kk x g y)
               (fact 'subterm-in-msgs tt kk x g)
               (dk-split-all!)
               (sml-pair-cond-intro! tt kk x b (lambda () (close kind x b (list g y))))))))))))

;; Run the device: RR from COND2, prove it a member of the power set and closed, cite
;; subterm-least, and land COND2(a, b) from (IS-SUBTERM tt kk a b).
(define (sml-device! tt kk a b cond2 close)
  (let ((rr `(SEP sip_ (SUBTERM-REL ,tt ,kk) ,(sml-pair-cond 'sip_ cond2))))
    (dk-have! `(IN ,rr (POWER ,(sml-box tt kk))) (lambda () (sml-subrel-power! tt kk rr)))
    (dk-have! `(IS-SUBTERM-CLOSED ,tt ,kk ,rr) (lambda () (sml-closed-pairs! tt kk rr close)))
    (fact 'subterm-least tt kk rr)
    (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                                (not (dk-contains? f 'IS-SUBTERM-CLOSED))))
                               (dk-asms))
                   (error "sml-device!: subterm-least did not detach"))
               a b)
    (sml-pair-cond-open! rr a b cond2)))

;;; INVERSION: a subterm of b is b itself, or b is the list message of a list and it is a
;;; subterm of a component, or b is an encryption and it is a subterm of the plaintext.
(define (sml-inv tt kk u v)
  `(OR (= ,u ,v)
       (OR (FORSOME sil_ (AND (IN sil_ (TUPLES (MSG-SET ,tt ,kk))) (AND (= ,v (LST sil_))
              (FORSOME sii_ (AND (IN sii_ NN) (AND (<= 1 sii_) (AND (<= sii_ (LENGTH sil_))
                                                                  (IS-SUBTERM ,tt ,kk ,u (NTH sii_ sil_)))))))))
           (FORSOME sig_ (AND (IN sig_ (MSG-SET ,tt ,kk))
              (FORSOME siy_ (AND (IN siy_ ,kk) (AND (= ,v (ENCR sig_ siy_)) (IS-SUBTERM ,tt ,kk ,u sig_)))))))))

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b)
    (OR (= a b)
        (OR (FORSOME l (AND (IN l (TUPLES (MSG-SET T K))) (AND (= b (LST l))
               (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH l)) (IS-SUBTERM T K a (NTH i l)))))))))
            (FORSOME g (AND (IN g (MSG-SET T K))
               (FORSOME y (AND (IN y K) (AND (= b (ENCR g y)) (IS-SUBTERM T K a g)))))))))))))))))
(dk-peel!)
(sml-device! 'T 'K 'a 'b (lambda (u v) (sml-inv 'T 'K u v))
  (lambda (kind x b info)
    (case kind
      ((refl) (oi-l) (rfl))
      ((list) (oi-r) (oi-l) (sml-ex-fill! (list (car info) (caddr info))))
      ((encr) (oi-r) (oi-r) (sml-ex-fill! info)))))
(dk-ass!)
(qed 'subterm-cases)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (FORALL c
    (IMPLIES (IS-SUBTERM T K a b) (IMPLIES (IS-SUBTERM T K b c) (IS-SUBTERM T K a c))))))))))))
(dk-peel!)
(let ((cond2 (lambda (u v) `(FORALL sia_ (IMPLIES (IS-SUBTERM T K sia_ ,u) (IS-SUBTERM T K sia_ ,v))))))
  (dk-apply!
    (sml-device! 'T 'K 'b 'c cond2
      (lambda (kind x b info)
        (case kind
          ((refl) (dk-peel!) (ass))
          ((list)
           (let* ((l (car info)) (prev (cadr info)) (i (caddr info))
                  (ih (sml-pair-cond-unpack! x prev cond2)))
             (dk-peel!)
             (let ((a1 (cadddr (dk-goal))))           ; (IS-SUBTERM T K a1 b)
               (dk-apply! ih a1)
               (fact 'subterm-in-msgs 'T 'K a1 prev)
               (dk-split-all!)
               (fact 'subterm-component 'T 'K a1 l i)
               (ass))))
          ((encr)
           (let* ((g (car info)) (y (cadr info))
                  (ih (sml-pair-cond-unpack! x g cond2)))
             (dk-peel!)
             (let ((a1 (cadddr (dk-goal))))
               (dk-apply! ih a1)
               (fact 'subterm-encr 'T 'K a1 g y)
               (ass)))))))
    'a)
  (ass))
(qed 'subterm-trans)

;; Is the existential D the list case (its first conjunct types the witness in a TUPLES)?
(define (sml-list-disjunct? d)
  (dk-head-is? (caddr (cadr (caddr d))) 'TUPLES))

;; The disjunction subterm-cases lands for (a, b), split: (ON-EQ) with (= a b) in context,
;; (ON-LIST l i) with b = LST(l), the typings and IS-SUBTERM(a, NTH(i, l)), (ON-ENCR g y) with
;; b = ENCR(g, y), the typings and IS-SUBTERM(a, g).
(define (sml-subterm-cases! tt kk a b on-eq on-list on-encr)
  (let ((o (dk-cite! 'subterm-cases tt kk a b)))
    (sml-or-each! o
      (lambda (d)
        (cond ((dk-head-is? d '=) (on-eq))
              ((sml-list-disjunct? d) (apply on-list (sml-unpack! d)))
              (#t (apply on-encr (sml-unpack! d))))))))

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (FORALL a (FORALL tk (IMPLIES (IN tk T) (IMPLIES (IS-SUBTERM T K a tk) (= a tk)))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(sml-subterm-cases! 'T 'K 'a 'tk
  (lambda () (ass))
  (lambda (l i)
    (sml-set-of! l '(TUPLES (MSG-SET T K)))
    (ai (dk-cite! 'token-ne-list 'T 'tk l)))
  (lambda (g y)
    (sml-set-of! g '(MSG-SET T K))
    (sml-set-of! y 'K)
    (ai (dk-cite! 'encr-ne-token 'T 'tk g y))))
(qed 'subterm-of-token)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IMPLIES (IS-SUBTERM T K a (LST l))
    (OR (= a (LST l))
        (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH l)) (IS-SUBTERM T K a (NTH i l)))))))))))))))))
(dk-peel!)
(fact 'list-in-msgs 'T 'K 'l)
(sml-subterm-cases! 'T 'K 'a '(LST l)
  (lambda () (oi-l) (ass))
  (lambda (l2 i)
    (fact 'lst-injective 'l l2)
    (oi-r)
    (subst `(= l ,l2))
    (sml-ex-fill! (list i)))
  (lambda (g y)
    (ai (dk-cite! 'lst-ne-encr 'l g y))))
(qed 'subterm-of-list)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL g (FORALL y (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
    (IMPLIES (IS-SUBTERM T K a (ENCR g y))
      (OR (= a (ENCR g y)) (IS-SUBTERM T K a g))))))))))))))
(dk-peel!)
(fact 'encr-in-msgs 'T 'K 'g 'y)
(sml-subterm-cases! 'T 'K 'a '(ENCR g y)
  (lambda () (oi-l) (ass))
  (lambda (l2 i)
    (ai (dk-cite! 'encr-ne-list 'g 'y l2)))
  (lambda (g2 y2)
    (fact 'encr-injective 'g 'y g2 y2)
    (dk-split-all!)
    (oi-r)
    (subst `(= g ,g2))
    (ass)))
(qed 'subterm-of-encr)

;;; A TOKEN that is a subterm of a list message is a subterm of one of its components (the
;;; token law rules out the token being the list message itself).  The adversary's C case.
(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (FORALL tk (FORALL l (IMPLIES (IN tk T) (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IMPLIES (IS-SUBTERM T K tk (LST l))
    (FORSOME i (AND (IN i NN) (AND (<= 1 i) (AND (<= i (LENGTH l)) (IS-SUBTERM T K tk (NTH i l)))))))))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(sml-set-of! 'l '(TUPLES (MSG-SET T K)))
(let ((o (dk-cite! 'subterm-of-list 'T 'K 'tk 'l)))
  (sml-or-each! o
    (lambda (d)
      (if (dk-head-is? d '=)
          (ai (dk-cite! 'token-ne-list 'T 'tk 'l))
          (ass)))))
(qed 'token-subterm-of-list)

;;; A TOKEN that is a subterm of an encryption is a subterm of the plaintext (the token law
;;; rules out the token being the encryption; the key is not a subterm).  The adversary's E case.
(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (FORALL tk (FORALL g (FORALL y (IMPLIES (IN tk T) (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
    (IMPLIES (IS-SUBTERM T K tk (ENCR g y)) (IS-SUBTERM T K tk g))))))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(sml-set-of! 'g '(MSG-SET T K))
(sml-set-of! 'y 'K)
(let ((o (dk-cite! 'subterm-of-encr 'T 'K 'tk 'g 'y)))
  (sml-or-each! o
    (lambda (d)
      (if (dk-head-is? d '=)
          (ai (dk-cite! 'encr-ne-token 'T 'tk 'g 'y))
          (ass)))))
(qed 'token-subterm-of-encr)

;;; PROPOSITION 2.12: y /= y2 and ENCR(h2, y2) @ ENCR(h, y) imply ENCR(h2, y2) @ h.  (The paper's
;;; K, K', h, h' are y, y2, h, h2.)
(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL h (FORALL h2 (FORALL y (FORALL y2
    (IMPLIES (IN h (MSG-SET T K)) (IMPLIES (IN h2 (MSG-SET T K)) (IMPLIES (IN y K) (IMPLIES (IN y2 K)
      (IMPLIES (NOT (= y y2))
        (IMPLIES (IS-SUBTERM T K (ENCR h2 y2) (ENCR h y)) (IS-SUBTERM T K (ENCR h2 y2) h)))))))))))))))))
(dk-peel!)
(fact 'encr-in-msgs 'T 'K 'h2 'y2)
(let ((o (dk-cite! 'subterm-of-encr 'T 'K '(ENCR h2 y2) 'h 'y)))
  (sml-or-each! o
    (lambda (d)
      (if (dk-head-is? d '=)
          (begin
            (fact 'encr-injective 'h2 'y2 'h 'y)
            (dk-split-all!)
            (dk-have! '(= y y2) (lambda () (subst '(= y2 y)) (rfl)))
            (ai '(NOT (= y y2))))
          (ass)))))
(qed 'subterm-encr-other-key)

;;; -----------------------------------------------------------------------
;;; 6. THE RANK: the least stage holding a message.

(sp (make-wff '(FORALL T (FORALL K (FORALL m (IMPLIES (IN m (MSG-SET T K))
   (AND (IN (MSG-RANK T K m) NN)
        (AND (IN m (MSG-STAGE T K (MSG-RANK T K m)))
             (FORALL j (IMPLIES (IN j NN) (IMPLIES (IN m (MSG-STAGE T K j)) (<= (MSG-RANK T K m) j))))))))))))
(dk-peel!)
(mac 'MSG-RANK)
(define sml-io
  (let find ((e (dk-goal)))
    (cond ((and (pair? e) (eq? (car e) 'IOTA)) e)
          ((pair? e) (or (find (car e)) (find (cdr e))))
          (#t #f))))
;; Does F contain an atom (<= X _)?
(define (sml-has-le? f x)
  (and (pair? f)
       (or (and (eq? (car f) '<=) (pair? (cdr f)) (equal? (cadr f) x))
           (any-pred (lambda (g) (sml-has-le? g x)) f))))
(define sml-ss '(SEP smw_ NN (IN m (MSG-STAGE T K smw_))))
(define (sml-in-ss! j)                   ; (IN j NN), (IN m (MSG-STAGE T K j)) in context
  (dk-have! `(IN ,j ,sml-ss) (lambda () (in-sep! (lambda () (ass)) (lambda () (ass))))))
(dk-each-leaf! (lambda () (iota-d sml-io))
  (lambda ()
    (if (not (dk-head-is? (dk-goal) 'FORSOME))
        (ass)
        (let* ((n0 (sml-set-open! 'm 'T 'K)))
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

;;; A list message in stage n has its list in TUPLES of a strictly earlier stage, and an
;;; encryption in stage n its plaintext in a strictly earlier stage (the token law: stage 0 holds
;;; neither; the tags: neither is the other).  Induction on the stage index, outermost.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (FORALL l
   (IMPLIES (IN l SET) (IMPLIES (IN (LST l) (MSG-STAGE T K n))
     (FORSOME j (AND (IN j NN) (AND (<= (succ j) n) (IN l (TUPLES (MSG-STAGE T K j))))))))))))))))
(define sml-cases3 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases3))
(dk-peel!)
(fact 'msg-stage-zero-elim 'T 'K '(LST l))
(fact 'lst-in-tuples-set 'l)
(ai (sml-token-law! 'T '(LST l)))
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases3))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (mem (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'MSG-STAGE))) landed))
       (x (cadr mem)) (l (cadr x))
       (tt (cadr (caddr mem))) (kk (caddr (caddr mem))) (n (cadr (cadddr (caddr mem))))
       (o (dk-cite! 'msg-stage-succ-cases tt kk n x)))
  (sml-or-each! o
    (lambda (d)
      (cond
        ((dk-head-is? d 'IN)
         (let ((j (dk-skolem! (dk-apply! ih tt kk l))))
           (ew j)
           (dk-conj-close!
             (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn! `(<= (succ ,j) ,n)) (ass))))))
        ((dk-head-is? (caddr (cadr (caddr d))) 'TUPLES)
         (let ((l2 (car (sml-unpack! d))))
           (fact 'lst-injective l l2)
           (ew n)
           (dk-conj-close!
             (lambda ()
               (cond ((dk-head-is? (dk-goal) '<=) (dk-nn!))
                     ((dk-asm? (dk-goal)) (ass))
                     (#t (subst `(= ,l ,l2)) (ass)))))))
        (#t
         (let* ((vs (sml-unpack! d)) (g (car vs)) (y (cadr vs)))
           (ai (dk-cite! 'lst-ne-encr l g y))))))))
(qed 'msg-stage-list-inv)

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (FORALL g (FORALL y
   (IMPLIES (IN g SET) (IMPLIES (IN y SET) (IMPLIES (IN (ENCR g y) (MSG-STAGE T K n))
     (FORSOME j (AND (IN j NN) (AND (<= (succ j) n) (IN g (MSG-STAGE T K j)))))))))))))))))
(define sml-cases4 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases4))
(dk-peel!)
(fact 'msg-stage-zero-elim 'T 'K '(ENCR g y))
(fact 'encr-in-tuples-set 'g 'y)
(ai (sml-token-law! 'T '(ENCR g y)))
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases4))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (mem (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'MSG-STAGE))) landed))
       (x (cadr mem)) (g (cadr x)) (y (caddr x))
       (tt (cadr (caddr mem))) (kk (caddr (caddr mem))) (n (cadr (cadddr (caddr mem))))
       (o (dk-cite! 'msg-stage-succ-cases tt kk n x)))
  (sml-or-each! o
    (lambda (d)
      (cond
        ((dk-head-is? d 'IN)
         (let ((j (dk-skolem! (dk-apply! ih tt kk g y))))
           (ew j)
           (dk-conj-close!
             (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn! `(<= (succ ,j) ,n)) (ass))))))
        ((dk-head-is? (caddr (cadr (caddr d))) 'TUPLES)
         (let ((l2 (car (sml-unpack! d))))
           (ai (dk-cite! 'encr-ne-list g y l2))))
        (#t
         (let* ((vs (sml-unpack! d)) (g2 (car vs)) (y2 (cadr vs)))
           (fact 'encr-injective g y g2 y2)
           (dk-split-all!)
           (ew n)
           (dk-conj-close!
             (lambda ()
               (cond ((dk-head-is? (dk-goal) '<=) (dk-nn!))
                     ((dk-asm? (dk-goal)) (ass))
                     (#t (subst `(= ,g ,g2)) (ass)))))))))))
(qed 'msg-stage-encr-inv)

;; rank-prop at the TYPED message x: land (IN rank NN), (IN x stage(rank)) and the minimality
;; universal; return the rank term.
(define (sml-rank! tt kk x)
  (fact 'msg-rank-prop tt kk x)
  (dk-split-all!)
  `(MSG-RANK ,tt ,kk ,x))
(define (sml-rank-min x)
  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (sml-has-le? f `(MSG-RANK T K ,x)))) (dk-asms))
      (error "sml-rank-min: no minimality for" x)))

(sp (make-wff '(FORALL T (FORALL K (FORALL tk (IMPLIES (IN tk T) (= (MSG-RANK T K tk) 0)))))))
(dk-peel!)
(fact 'token-in-msgs 'T 'K 'tk)
(fact 'msg-stage-token 'T 'K 'tk)
(fact 'nn-zero-in)
(let ((r (sml-rank! 'T 'K 'tk)))
  (dk-apply! (sml-rank-min 'tk) 0)
  (dk-nn! `(<= ,r 0)))
(qed 'msg-rank-token)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (FORALL l (FORALL i
   (IMPLIES (IN l (TUPLES (MSG-SET T K))) (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
     (<= (succ (MSG-RANK T K (NTH i l))) (MSG-RANK T K (LST l))))))))))))))
(dk-peel!)
(fact 'list-in-msgs 'T 'K 'l)
(sml-set-of! 'l '(TUPLES (MSG-SET T K)))
(sml-nth-in! '(MSG-SET T K) 'i 'l)
(let* ((rl (sml-rank! 'T 'K '(LST l)))
       (rc (sml-rank! 'T 'K '(NTH i l)))
       (j (dk-skolem! (dk-cite! 'msg-stage-list-inv rl 'T 'K 'l))))
  (sml-nth-in! `(MSG-STAGE T K ,j) 'i 'l)
  (dk-apply! (sml-rank-min '(NTH i l)) j)
  (dk-nn! `(<= ,rc ,j) `(<= (succ ,j) ,rl)))
(qed 'msg-rank-component)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (FORALL g (FORALL y
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
     (<= (succ (MSG-RANK T K g)) (MSG-RANK T K (ENCR g y))))))))))))
(dk-peel!)
(fact 'encr-in-msgs 'T 'K 'g 'y)
(sml-set-of! 'g '(MSG-SET T K))
(sml-set-of! 'y 'K)
(let* ((re (sml-rank! 'T 'K '(ENCR g y)))
       (rg (sml-rank! 'T 'K 'g))
       (j (dk-skolem! (dk-cite! 'msg-stage-encr-inv re 'T 'K 'g 'y))))
  (dk-apply! (sml-rank-min 'g) j)
  (dk-nn! `(<= ,rg ,j) `(<= (succ ,j) ,re)))
(qed 'msg-rank-encr)

;;; A proper subterm has a strictly smaller rank; so the subterm relation is ANTISYMMETRIC,
;;; a partial order (reflexive: subterm-refl; transitive: subterm-trans).
(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b)
    (OR (= a b) (<= (succ (MSG-RANK T K a)) (MSG-RANK T K b))))))))))))
(dk-peel!)
(fact 'token-set-is-set 'T)
(let ((cond2 (lambda (u v) `(OR (= ,u ,v) (<= (succ (MSG-RANK T K ,u)) (MSG-RANK T K ,v))))))
  (sml-device! 'T 'K 'a 'b cond2
    (lambda (kind x b info)
      (case kind
        ((refl) (oi-l) (rfl))
        ((list)
         (let* ((l (car info)) (prev (cadr info)) (i (caddr info))
                (ih (sml-pair-cond-unpack! x prev cond2)))
           (fact 'msg-rank-component 'T 'K l i)
           (dk-each-leaf! (lambda () (ai ih))
             (lambda ()
               (oi-r)
               (if (dk-asm? `(= ,x ,prev))
                   (begin (subst `(= ,x ,prev)) (ass))
                   (let* ((rx (sml-rank! 'T 'K x)) (rp (sml-rank! 'T 'K prev)) (rb (sml-rank! 'T 'K b)))
                     (dk-nn! `(<= (succ ,rx) ,rp) `(<= (succ ,rp) ,rb))))))))
        ((encr)
         (let* ((g (car info)) (y (cadr info))
                (ih (sml-pair-cond-unpack! x g cond2)))
           (fact 'msg-rank-encr 'T 'K g y)
           (dk-each-leaf! (lambda () (ai ih))
             (lambda ()
               (oi-r)
               (if (dk-asm? `(= ,x ,g))
                   (begin (subst `(= ,x ,g)) (ass))
                   (let* ((rx (sml-rank! 'T 'K x)) (rg (sml-rank! 'T 'K g)) (rb (sml-rank! 'T 'K b)))
                     (dk-nn! `(<= (succ ,rx) ,rg) `(<= (succ ,rg) ,rb)))))))))))
  (dk-ass!))
(qed 'subterm-rank)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b) (IMPLIES (IS-SUBTERM T K b a) (= a b)))))))))))
(dk-peel!)
(fact 'subterm-in-msgs 'T 'K 'a 'b)
(dk-split-all!)
(let* ((o1 (dk-cite! 'subterm-rank 'T 'K 'a 'b))
      (o2 (dk-cite! 'subterm-rank 'T 'K 'b 'a)))
  (dk-each-leaf! (lambda () (ai o1))
    (lambda ()
      (if (dk-asm? '(= a b))
          (ass)
          (dk-each-leaf! (lambda () (ai o2))
            (lambda ()
              (if (dk-asm? '(= b a))
                  (dk-have! '(= a b) (lambda () (subst '(= a b)) (rfl)))
                  (let* ((ra (sml-rank! 'T 'K 'a)) (rb (sml-rank! 'T 'K 'b)))
                    (dk-have! '(< 0 0)
                      (lambda () (dk-nn! `(<= (succ ,ra) ,rb) `(<= (succ ,rb) ,ra))))
                    (fact 'rr-zero-in)
                    (ai (dk-cite! 'rr-lt-irrefl 0))))))))))
(qed 'subterm-antisym)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing))
          '(pair-self-member pair-self-eq msg-set-unfold subterm-rel-unfold pair-in-cartesian-parts
            lst-unfold encr-unfold cartesian3-set))
(for-each (lambda (n) (topic! n 'constructions))
          '(encr-ne-list lst-ne-encr lst-injective encr-injective
            msg-stage-token msg-stage-keep msg-stage-list msg-stage-encr msg-stage-zero-elim
            msg-stage-succ-cases msg-stage-add msg-set-intro msg-set-elim token-in-msgs msg-stage-set
            msg-set-is-set msg-lists-are-lists list-in-some-stage list-in-msgs encr-in-msgs
            lst-in-tuples-set encr-in-tuples-set token-set-is-set token-not-list token-ne-list
            encr-ne-token msg-induction msg-cases subterm-in-msgs subterm-least subterm-refl
            subterm-component subterm-encr subterm-cases subterm-trans subterm-of-token
            subterm-of-list subterm-of-encr token-subterm-of-list token-subterm-of-encr
            subterm-encr-other-key msg-rank-prop msg-stage-list-inv msg-stage-encr-inv
            msg-rank-token msg-rank-component msg-rank-encr subterm-rank subterm-antisym))
