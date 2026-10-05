;;; strand-messages-laws.scm -- THE MESSAGE ALGEBRA OF STRAND SPACES: its laws.
;;; (Thayer, Herzog, Guttman, "Strand Spaces: Proving Security Protocols Correct",
;;;  ~/docs/jcs_strand_spaces.pdf, sections 2.3-2.4: Axioms 1 and 2, Definition 2.11,
;;;  Proposition 2.12.)  Agent S-1 of the October roadmap, week 3, 2026-10-04.
;;; The definitions are structure-library/strand-messages.scm; the design is
;;; docs/strand-spaces-design-2026-10-03.md.  Helper prefix: sml-.
;;;
;;; Every theorem below bills `modulo 0'.  The oracles that appear on some of
;;; them are `arith' (ground numeral facts: 0 /= 1, 2 in NN, for the tags) and
;;; `ineq' (NN linear arithmetic, through dk-nn!, for the rank).  Nothing is
;;; asserted, stamped or warranted.  T and K are the texts and the keys; A is
;;; MSG-SET(T, K); "message" means a member of A.
;;;
;;; WHAT IS PROVEN (56 theorems, in this order)
;;;  1. atom-unfold, cat-unfold, enc-unfold          the constructors as citable == equations
;;;  2. FREENESS (the paper's Axioms 1 and 2 are theorems of the encoding):
;;;     atom-ne-cat, atom-ne-enc, cat-ne-enc         pairwise disjoint ranges (the tag)
;;;     atom-injective, cat-injective, enc-injective (list components, NTH)
;;;  3. pair-self-member, pair-self-eq               a set is the one member of PAIR(a, a)
;;;  4. msg-stage-atom, -keep, -cat, -enc            the stage clauses, introduction
;;;  5. msg-stage-zero-cases, msg-stage-succ-cases   ... and elimination
;;;  6. msg-stage-add                                S_j is included in S_(j + d)
;;;  7. msg-set-unfold, msg-set-intro, msg-set-elim  A is the union of the stages
;;;  8. atom-in-msgs, cat-in-msgs, enc-in-msgs       the constructors build messages
;;;  9. msg-induction                                STRUCTURAL INDUCTION, class form
;;; 10. msg-cases                                    every message is an atom, a CAT or an ENC
;;; 11. cartesian3-set, msg-stage-set, msg-set-is-set   sethood (replacement for the triples)
;;; 12. message-algebra-msgs, texts-keys-disjoint, kinv-in-fun, kinv-involution,
;;;     kinv-injective                               the structure's projections
;;; 13. pair-in-cartesian-parts, subterm-rel-unfold, subterm-in-msgs, subterm-least,
;;;     subterm-refl, subterm-enc, subterm-cat-left, subterm-cat-right
;;;                                                  Definition 2.11: the clauses, minimality
;;; 14. subterm-cases (INVERSION), subterm-trans, subterm-of-atom, subterm-of-enc,
;;;     subterm-of-cat, subterm-enc-other-key (PROPOSITION 2.12)
;;; 15. msg-rank-prop (the IOTA denotes), msg-stage-enc-inv, msg-stage-cat-inv,
;;;     msg-rank-atom, msg-rank-enc, msg-rank-cat     the rank and its laws
;;; 16. subterm-rank, subterm-antisym                a proper subterm has smaller rank;
;;;                                                  the subterm relation is a partial order
;;;
;;; THE TECHNIQUE.  (a) Stage hypotheses are opened on a LANE (there is no
;;; hypothesis-side subst): the claim (IN m BODY) is proved by rewriting BODY back to
;;; the stage term.  (b) Cartesian membership is opened by proving the implication
;;; mem => chain with the primitive cartesian-decompose macete fired on its antecedent;
;;; the chain is written with fixed binders cdv1_, cdv2_, ... so that the printed page
;;; carries no counter-minted name.  (c) Every property of the subterm relation that
;;; is not one of its four clauses is ONE device: subterm-least at the separation
;;;     RR = { p in SUBTERM-REL(T, K) : exists u, v. p = [u, v] and COND(u, v) },
;;; shown to be in POWER(A x A) (a set, as T and K are) and closed under the four
;;; clauses; then every subterm pair satisfies COND.  COND is the inversion
;;; disjunction for subterm-cases, "every subterm of u is one of v" for
;;; subterm-trans, and "u = v or rank u < rank v" for subterm-rank.  `sml-closed-pairs!'
;;; reduces each closure obligation to the one fact the new pair needs.
;;; (d) The rank is an IOTA: `iota-d' with existence from nn-least-element over the
;;; stage indices holding m, uniqueness from nn-le-antisym.
;;;
;;; TYPE BEFORE YOU INSTANTIATE: a predicate hypothesis IS-SUBTERM(T, K, a, ENC(g, y))
;;; does not certify ENC(g, y) as defined, so every compound right-hand side is typed
;;; (enc-in-msgs / cat-in-msgs) before anything is instantiated at it; that is why
;;; subterm-of-enc, subterm-of-cat and Proposition 2.12 carry the typings of the
;;; components (the paper's terms and keys range over A and K anyway).
;;;
;;; LOAD WINDOW [lo, hi): lo = theorem-library/nn-least-element (load.scm line 1732),
;;; the latest citation; the others: nn-order-proof (1172: nn-le-antisym),
;;; nn-parity-proof (953: nn-succ-plus-one, through dk-nn!), subset-lemmas (940:
;;; subclass-of-set-is-set), rr-order-basics (826: rr-lt-irrefl), nn-order-basics
;;; (798: nn-in-rr), nn-order-ord (791: nn-zero-le), pair-tuple-sethood (776:
;;; pair-in-cartesian), structure-library/injection (411: image-set), the base theory
;;; and number-systems (primitive).  No late tactic (dk-nn!, dk-ineq! and ineq load
;;; early).  hi = none yet (no citer).  structure-library/strand-messages must load
;;; before this file and after structure-library/ordinals (def-by-nn-recursion).

;;; -----------------------------------------------------------------------
;;; helpers (prefix sml-)

;; `keep' the named formulas and close by `prop' -- unless `keep' found the kept
;; sequent already proven, which GROUNDS the focus leaf (a bare `prop' after it
;; would run on whatever leaf has the focus next).
(define (sml-keep-prop! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply dk-only! fs)
    (if (not (sequent-node-grounded? node)) (prop))))

;; (= L1 L2) in context, L1 and L2 literal lists whose first entries are two
;; DIFFERENT numerals: close the FALSITY goal.  The tag is read off both sides
;; by NTH 1 (nth-r), the equation is used by `subst' (no congruence rule).
(define (sml-tag-absurd! l1 l2)
  (let ((t1 (cadr l1)) (t2 (cadr l2)))
    (dk-have! `(= (NTH 1 ,l2) ,t2) (lambda () (nth-r) (rfl)))
    (dk-have! `(= ,t1 (NTH 1 ,l2)) (lambda () (subst `(= ,l2 ,l1)) (nth-r) (rfl)))
    (dk-have! `(= ,t1 ,t2) (lambda () (subst `(= ,t2 (NTH 1 ,l2))) (ass)))
    (dk-have! `(NOT (= ,t1 ,t2)) (lambda () (arith)))
    (ai `(NOT (= ,t1 ,t2)))))

;; (= L1 L2) in context, literal lists of one length; the goal (= x y) with x the
;; I-th entry of L1 and y the I-th entry of L2: rewrite y to NTH I L2, L2 to L1,
;; reduce.
(define (sml-component! l1 l2 i)
  (let* ((x (list-ref l1 i)) (y (list-ref l2 i)))
    (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
    (subst `(= ,y (NTH ,i ,l2)))
    (subst `(= ,l2 ,l1))
    (nth-r)
    (rfl)))

;; The goal an AND of component equations (= x_i y_i) between the entries of
;; the literal lists L1, L2, (= L1 L2) in context: split, and close each leaf
;; by `sml-component!' at the index its left-hand side sits at in L1.
(define (sml-components! l1 l2)
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (let* ((g (dk-goal))
             (i (let loop ((k 1))
                  (cond ((> k (- (length l1) 1)) (error "sml-components!: no index for" g))
                        ((and (equal? (list-ref l1 k) (cadr g))
                              (equal? (list-ref l2 k) (caddr g))) k)
                        (else (loop (+ k 1)))))))
        (sml-component! l1 l2 i)))))

;;; -----------------------------------------------------------------------
;;; 1. The constructors as citable equations (mac-h cannot unfold a functoid in an
;;;    assumption by the functoid's own name; these are what it can name).

(sp (make-wff '(FORALL a (== (ATOM a) (LIST 0 a)))))
(di) (mac 'ATOM) (qrfl)
(qed 'atom-unfold)

(sp (make-wff '(FORALL g (FORALL h (== (CAT g h) (LIST 1 g h))))))
(di) (mac 'CAT) (qrfl)
(qed 'cat-unfold)

(sp (make-wff '(FORALL g (FORALL k (== (ENC g k) (LIST 2 g k))))))
(di) (mac 'ENC) (qrfl)
(qed 'enc-unfold)

;;; -----------------------------------------------------------------------
;;; 2. FREENESS (the paper's Axioms 1 and 2, here theorems of the encoding).

(sp (make-wff '(FORALL a (FORALL g (FORALL h (NOT (= (ATOM a) (CAT g h))))))))
(di) (mac 'ATOM) (mac 'CAT) (di)
(sml-tag-absurd! '(LIST 0 a) '(LIST 1 g h))
(qed 'atom-ne-cat)

(sp (make-wff '(FORALL a (FORALL g (FORALL k (NOT (= (ATOM a) (ENC g k))))))))
(di) (mac 'ATOM) (mac 'ENC) (di)
(sml-tag-absurd! '(LIST 0 a) '(LIST 2 g k))
(qed 'atom-ne-enc)

(sp (make-wff '(FORALL g (FORALL h (FORALL u (FORALL k (NOT (= (CAT g h) (ENC u k)))))))))
(di) (mac 'CAT) (mac 'ENC) (di)
(sml-tag-absurd! '(LIST 1 g h) '(LIST 2 u k))
(qed 'cat-ne-enc)

(sp (make-wff '(FORALL a (FORALL b (IMPLIES (= (ATOM a) (ATOM b)) (= a b))))))
(di) (mac 'ATOM) (di)
(sml-component! '(LIST 0 a) '(LIST 0 b) 2)
(qed 'atom-injective)

(sp (make-wff '(FORALL g (FORALL h (FORALL u (FORALL v
   (IMPLIES (= (CAT g h) (CAT u v)) (AND (= g u) (= h v)))))))))
(di) (mac 'CAT) (di)
(sml-components! '(LIST 1 g h) '(LIST 1 u v))
(qed 'cat-injective)

(sp (make-wff '(FORALL g (FORALL k (FORALL u (FORALL y
   (IMPLIES (= (ENC g k) (ENC u y)) (AND (= g u) (= k y)))))))))
(di) (mac 'ENC) (di)
(sml-components! '(LIST 2 g k) '(LIST 2 u y))
(qed 'enc-injective)

;;; -----------------------------------------------------------------------
;;; 3. The tags: a set is the only member of its own singleton PAIR(a, a).

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
;;; helpers for the stages

;; (IN n SET) for a numeral tag n (0, 1, 2), through n in NN.
(define (sml-num-set! n)
  (dk-have! `(IN ,n SET)
    (lambda ()
      (dk-have! `(IN ,n NN) (lambda () (arith)))
      (fact 'membership-implies-sethood n 'NN)
      (ass))))

;; Close the focus goal (IN x C) where x is a term and C is built from UNION,
;; CARTESIAN and PAIR(n, n) around classes x's pieces are typed in, in context.
;; At a UNION, the side is chosen by a pure test (sml-fits?) before any step.
(define (sml-fits? x c)
  (cond ((dk-asm? `(IN ,x ,c)) #t)
        ((and (pair? c) (eq? (car c) 'PAIR)) (equal? x (cadr c)))
        ((and (pair? c) (eq? (car c) 'UNION)) (or (sml-fits? x (cadr c)) (sml-fits? x (caddr c))))
        ((and (pair? c) (eq? (car c) 'CARTESIAN) (pair? x) (eq? (car x) 'LIST)
              (= (length x) (length c)))
         (let loop ((xs (cdr x)) (cs (cdr c)))
           (or (null? xs) (and (sml-fits? (car xs) (car cs)) (loop (cdr xs) (cdr cs))))))
        (else #f)))

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
      (else (error "sml-close-in!: no route" (expression->string g))))))

;; The stage equation at n (n = 0 or (succ j) with j in NN in context), landed
;; and returned.
(define (sml-stage-eq tt kk n)
  (if (equal? n 0)
      (dk-cite! 'msg-stage-zero tt kk)
      (dk-cite! 'msg-stage-succ tt kk (cadr n))))

;;; -----------------------------------------------------------------------
;;; 4. The stages: introduction.

(sp (make-wff '(FORALL T (FORALL K (FORALL a
   (IMPLIES (IN a (UNION T K)) (IN (ATOM a) (MSG-STAGE T K 0))))))))
(di)
(subst (sml-stage-eq 'T 'K 0))
(mac 'ATOM)
(sml-close-in!)
(qed 'msg-stage-atom)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T K n)) (IN m (MSG-STAGE T K (succ n)))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(sml-close-in!)
(qed 'msg-stage-keep)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL g (FORALL h
   (IMPLIES (IN n NN) (IMPLIES (IN g (MSG-STAGE T K n)) (IMPLIES (IN h (MSG-STAGE T K n))
      (IN (CAT g h) (MSG-STAGE T K (succ n)))))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(mac 'CAT)
(sml-close-in!)
(qed 'msg-stage-cat)

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL g (FORALL y
   (IMPLIES (IN n NN) (IMPLIES (IN g (MSG-STAGE T K n)) (IMPLIES (IN y K)
      (IN (ENC g y) (MSG-STAGE T K (succ n)))))))))))))
(dk-peel!)
(subst (sml-stage-eq 'T 'K '(succ n)))
(mac 'ENC)
(sml-close-in!)
(qed 'msg-stage-enc)

;;; -----------------------------------------------------------------------
;;; helpers for the eliminations

;; Skolemise the FORSOME EX in context and every FORSOME that lands from it,
;; outermost first; returns the eigenvariables in order.  A tag membership
;; (IN v (PAIR n n)) that lands is turned into (= v n) at once.
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

;; The goal (= m X), X built by the constructors: unfold them, replace m by the
;; literal list the context equates it with, the tag variables by their numerals.
(define (sml-eq-close!)
  (for-each (lambda (f) (if (dk-contains? (dk-goal) f) (mac f))) '(ATOM CAT ENC))
  (if (equal? (cadr (dk-goal)) (caddr (dk-goal)))
      (rfl)
      (sml-eq-close--subst!)))

(define (sml-eq-close--subst!)
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
    (rfl)))

;; Close an existential goal FORSOME x1 (AND (IN x1 C1) (FORSOME x2 ... (= m X)))
;; with the witnesses WS: memberships by sml-close-in!, the equation by sml-eq-close!.
(define (sml-ex-close! ws)
  (if (null? ws)
      (sml-eq-close!)
      (begin
        (ew (car ws))
        (dk-each-leaf! (lambda () (di))
          (lambda ()
            (cond ((dk-head-is? (dk-goal) 'FORSOME) (sml-ex-close! (cdr ws)))
                  ((dk-head-is? (dk-goal) '=) (sml-eq-close!))
                  (else (sml-close-in!))))))))

;; (IN m (MSG-STAGE tt kk n)) in context: land and return (IN m BODY), BODY the
;; right-hand side of the stage equation (there is no hypothesis-side subst: the
;; claim is proved on a lane by rewriting BODY back to the stage).
(define (sml-stage-open! m tt kk n)
  (let* ((eqn (sml-stage-eq tt kk n))
         (body (caddr eqn))
         (claim `(IN ,m ,body)))
    (dk-have! claim (lambda () (subst `(= ,body (MSG-STAGE ,tt ,kk ,n))) (ass)))
    claim))

;; (IN x (CARTESIAN C1 ... Cn)) in context: land and return the existential
;; chain the primitive `cartesian-decompose' schema reads it as.  The chain is
;; written here with FIXED binders cdv1_, cdv2_, ... (the macete's own builder
;; mints counter names, which a printed page cannot reproduce), and the
;; implication is proved by firing the macete on its antecedent (`ass' is alpha-aware).
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

;;; -----------------------------------------------------------------------
;;; 5. The stages: elimination (every member of a stage was built by one clause).

(sp (make-wff '(FORALL T (FORALL K (FORALL m
   (IMPLIES (IN m (MSG-STAGE T K 0))
            (FORSOME a (AND (IN a (UNION T K)) (= m (ATOM a))))))))))
(di)
(sml-stage-open! 'm 'T 'K 0)
(let ((vs (sml-unpack! (sml-cart-open! '(IN m (CARTESIAN (PAIR 0 0) (UNION T K)))))))
  (sml-ex-close! (list (cadr vs))))
(qed 'msg-stage-zero-cases)

(define sml-sn '(MSG-STAGE T K n))
(define sml-c1 '(CARTESIAN (PAIR 1 1) (MSG-STAGE T K n) (MSG-STAGE T K n)))
(define sml-c2 '(CARTESIAN (PAIR 2 2) (MSG-STAGE T K n) K))

(sp (make-wff '(FORALL T (FORALL K (FORALL n (FORALL m
   (IMPLIES (IN n NN) (IMPLIES (IN m (MSG-STAGE T K (succ n)))
     (OR (IN m (MSG-STAGE T K n))
         (OR (FORSOME g (AND (IN g (MSG-STAGE T K n))
                             (FORSOME h (AND (IN h (MSG-STAGE T K n)) (= m (CAT g h))))))
             (FORSOME g (AND (IN g (MSG-STAGE T K n))
                             (FORSOME y (AND (IN y K) (= m (ENC g y))))))))))))))))
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

;;; -----------------------------------------------------------------------
;;; 6. The stages grow: S_j is included in S_(j + d).  The induction variable d
;;;    is OUTERMOST, as `ni' needs it.

(sp (make-wff '(FORALL d (IMPLIES (IN d NN)
   (FORALL T (FORALL K (FORALL j (FORALL m
     (IMPLIES (IN j NN) (IMPLIES (IN m (MSG-STAGE T K j)) (IN m (MSG-STAGE T K (+ j d)))))))))))))
(define sml-cases (dk-opened (lambda () (ni))))
(define (sml-step-case? g)
  (and (dk-head-is? g 'FORALL) (dk-head-is? (caddr g) 'IMPLIES)
       (dk-head-is? (cadr (caddr g)) 'IN) (eq? (caddr (cadr (caddr g))) 'NN)))
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
;;; 7. The message set.

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

;; (IN x (MSG-SET tt kk)) in context: land a stage index and the stage
;; membership; return the index.
(define (sml-set-open! x tt kk)
  (let* ((ex (dk-cite! 'msg-set-elim tt kk x)))
    (dk-skolem! ex)))

;; Land (IN x (MSG-STAGE tt kk (+ i j))) from (IN x (MSG-STAGE tt kk i)), i, j in NN.
(define (sml-lift! x tt kk i j)
  (fact 'msg-stage-add j tt kk i x)
  (dk-ctx-form `(IN ,x (MSG-STAGE ,tt ,kk (+ ,i ,j)))))

;;; -----------------------------------------------------------------------
;;; 8. The constructors build messages.

(sp (make-wff '(FORALL T (FORALL K (FORALL a
   (IMPLIES (IN a (UNION T K)) (IN (ATOM a) (MSG-SET T K))))))))
(dk-peel!)
(fact 'msg-stage-atom 'T 'K 'a)
(fact 'nn-zero-in)
(fact 'msg-set-intro 'T 'K 0 '(ATOM a))
(ass)
(qed 'atom-in-msgs)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (FORALL h
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN h (MSG-SET T K)) (IN (CAT g h) (MSG-SET T K))))))))))
(dk-peel!)
(let* ((i (sml-set-open! 'g 'T 'K))
       (j (sml-set-open! 'h 'T 'K)))
  (sml-lift! 'g 'T 'K i j)
  (sml-lift! 'h 'T 'K j i)
  (dk-have! `(AND (IN ,i NN) (IN ,j NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'nn-add-closed i j)
  (fact 'nn-add-comm i j)
  (dk-have! `(IN h (MSG-STAGE T K (+ ,i ,j))) (lambda () (subst `(= (+ ,i ,j) (+ ,j ,i))) (ass)))
  (fact 'msg-stage-cat 'T 'K `(+ ,i ,j) 'g 'h)
  (fact 'nn-succ-closed `(+ ,i ,j))
  (fact 'msg-set-intro 'T 'K `(succ (+ ,i ,j)) '(CAT g h))
  (ass))
(qed 'cat-in-msgs)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (FORALL y
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K) (IN (ENC g y) (MSG-SET T K))))))))))
(dk-peel!)
(let ((i (sml-set-open! 'g 'T 'K)))
  (fact 'msg-stage-enc 'T 'K i 'g 'y)
  (fact 'nn-succ-closed i)
  (fact 'msg-set-intro 'T 'K `(succ ,i) '(ENC g y))
  (ass))
(qed 'enc-in-msgs)

;;; -----------------------------------------------------------------------
;;; 9. STRUCTURAL INDUCTION (the paper's "inductive definition" made usable):
;;;    a class C holding the atoms and closed under CAT and ENC on messages
;;;    holds every message.  By `ni' on the stage index, on a lane.

(sp (make-wff '(FORALL T (FORALL K (FORALL C
   (IMPLIES (FORALL a (IMPLIES (IN a (UNION T K)) (IN (ATOM a) C)))
   (IMPLIES (FORALL g (FORALL h (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN h (MSG-SET T K))
              (IMPLIES (IN g C) (IMPLIES (IN h C) (IN (CAT g h) C)))))))
   (IMPLIES (FORALL g (FORALL y (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
              (IMPLIES (IN g C) (IN (ENC g y) C))))))
     (FORALL m (IMPLIES (IN m (MSG-SET T K)) (IN m C)))))))))))
(let* ((landed (dk-peel!))
       (g0 (dk-goal)) (m0 (cadr g0))
       (tt 'T) (kk 'K) (cc (caddr g0))
       ;; the three hypotheses, told apart by the constructor in their consequent
       (hyp-with (lambda (ctor)
                   (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f ctor)
                                                    (dk-contains? f cc)))
                                   landed)
                       (error "msg-induction: no hypothesis for" ctor))))
       (h-atom (hyp-with 'ATOM)) (h-cat (hyp-with 'CAT)) (h-enc (hyp-with 'ENC))
       (claim `(FORALL smn_ (IMPLIES (IN smn_ NN)
                 (FORALL smm_ (IMPLIES (IN smm_ (MSG-STAGE ,tt ,kk smn_)) (IN smm_ ,cc)))))))
  (dk-have! claim
    (lambda ()
      (let ((cases (dk-opened (lambda () (ni)))))
        ;; base: a member of stage 0 is an atom
        (dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) cases))
        (dk-peel!)
        (let* ((m (cadr (dk-goal)))
               (ex (dk-cite! 'msg-stage-zero-cases tt kk m))
               (a (dk-skolem! ex)))
          (subst `(= ,m (ATOM ,a)))
          (dk-apply! h-atom a)
          (ass))
        ;; step: a member of stage succ n is kept, or a CAT, or an ENC of stage-n messages
        (dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) cases))
        (let* ((landed (dk-peel!))
               (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
               (m (cadr (dk-goal)))
               (n (cadr (cadddr (caddr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) m)))
                                                   landed)))))
               (o (dk-cite! 'msg-stage-succ-cases tt kk n m)))
          (dk-each-leaf! (lambda () (ai o))
            (lambda ()
              (cond
                ((dk-asm? `(IN ,m (MSG-STAGE ,tt ,kk ,n)))
                 (dk-apply! ih m) (ass))
                (else
                 (let ((o2 (or (find-first (lambda (f) (dk-head-is? f 'OR)) (dk-asms))
                               (error "msg-induction: no second disjunction"))))
                   (dk-each-leaf! (lambda () (ai o2))
                     (lambda ()
                       (let* ((ex (find-first (lambda (f) (and (dk-head-is? f 'FORSOME)
                                                               (dk-contains? f m)))
                                              (dk-asms)))
                              (catp (dk-contains? ex 'CAT))
                              (vs (sml-unpack! ex))
                              (g (car vs)) (h (cadr vs)))
                         (subst (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) m)))
                                            (dk-asms)))
                         (dk-apply! ih g)
                         (fact 'msg-set-intro tt kk n g)
                         (if catp
                             (begin (dk-apply! ih h)
                                    (fact 'msg-set-intro tt kk n h)
                                    (dk-apply! h-cat g h))
                             (dk-apply! h-enc g h))
                         (ass)))))))))))))
  ;; the message is in some stage, and the claim holds there
  (let ((n (sml-set-open! m0 tt kk)))
    (dk-apply! claim n m0)
    (ass)))
(qed 'msg-induction)

;;; -----------------------------------------------------------------------
;;; 10. Every message is an atom, a concatenation of messages or an encryption
;;;     of a message under a key: msg-induction at the class of messages that are.

(define (sml-cases-of z)
  `(OR (FORSOME a (AND (IN a (UNION T K)) (= ,z (ATOM a))))
       (OR (FORSOME g (AND (IN g (MSG-SET T K)) (FORSOME h (AND (IN h (MSG-SET T K)) (= ,z (CAT g h))))))
           (FORSOME g (AND (IN g (MSG-SET T K)) (FORSOME y (AND (IN y K) (= ,z (ENC g y)))))))))

(sp (make-wff `(FORALL T (FORALL K (FORALL m (IMPLIES (IN m (MSG-SET T K)) ,(sml-cases-of 'm)))))))
(dk-peel!)
(let* ((cc `(SEP smz_ (MSG-SET T K) ,(sml-cases-of 'smz_)))
       (h1 `(FORALL a (IMPLIES (IN a (UNION T K)) (IN (ATOM a) ,cc))))
       (h2 `(FORALL g (FORALL h (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN h (MSG-SET T K))
              (IMPLIES (IN g ,cc) (IMPLIES (IN h ,cc) (IN (CAT g h) ,cc))))))))
       (h3 `(FORALL g (FORALL y (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
              (IMPLIES (IN g ,cc) (IN (ENC g y) ,cc))))))))
  (dk-have! h1
    (lambda ()
      (dk-peel!)
      (in-sep! (lambda () (fact 'atom-in-msgs 'T 'K 'a) (ass))
               (lambda () (oi-l) (sml-ex-close! '(a))))))
  (dk-have! h2
    (lambda ()
      (dk-peel!)
      (in-sep! (lambda () (fact 'cat-in-msgs 'T 'K 'g 'h) (ass))
               (lambda () (oi-r) (oi-l) (sml-ex-close! '(g h))))))
  (dk-have! h3
    (lambda ()
      (dk-peel!)
      (in-sep! (lambda () (fact 'enc-in-msgs 'T 'K 'g 'y) (ass))
               (lambda () (oi-r) (oi-r) (sml-ex-close! '(g y))))))
  (fact 'msg-induction 'T 'K cc)
  (dk-apply! (or (dk-ctx-form `(FORALL m (IMPLIES (IN m (MSG-SET T K)) (IN m ,cc))))
                 (error "msg-cases: the induction did not detach"))
             'm)
  (sep-me `(IN m ,cc))
  (ass))
(qed 'msg-cases)

;;; -----------------------------------------------------------------------
;;; 11. SETHOOD: a stage, and the message set, are sets when T and K are.
;;;     The ternary product is a set by REPLACEMENT over the binary product
;;;     U x (V x W): it is included in the image of [a, [b, c]] |-> [a, b, c].

;; (IN t SET) for t built from symbols / stages with a sethood in context,
;; numeral singletons PAIR(n, n), UNION and CARTESIAN (binary or ternary).
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
      (else (error "sml-set!: no route to the sethood of" (expression->string t))))))

;; The focus goal (IN t SET): land it by sml-set! and close it, unless the landing
;; already closed it in place (dk-have! of a claim equal to the focus goal does).
(define (sml-set-close!)
  (let ((g (dk-goal)))
    (sml-set! (cadr g))
    (if (and (alpha-equiv? (dk-goal) g) (dk-asm? g)) (ass))))

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
(sml-set-close!)
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

;;; -----------------------------------------------------------------------
;;; 12. The structure: the projections a later statement needs.

(sp (make-wff '(FORALL alg (IMPLIES (IS-MESSAGE-ALGEBRA alg)
   (AND (IN (TEXTS alg) SET) (AND (IN (KEYS alg) SET) (= (MSGS alg) (MSG-SET (TEXTS alg) (KEYS alg)))))))))
(dk-peel!)
(mac-h 'is-message-algebra '(IS-MESSAGE-ALGEBRA alg))
(dk-split-all!)
(dk-conj-close! (lambda () (ass)))
(qed 'message-algebra-msgs)

(sp (make-wff '(FORALL alg (IMPLIES (IS-MESSAGE-ALGEBRA alg)
   (FORALL x (IMPLIES (IN x (TEXTS alg)) (NOT (IN x (KEYS alg)))))))))
(dk-peel!)
(mac-h 'is-message-algebra '(IS-MESSAGE-ALGEBRA alg))
(dk-split-all!)
(dk-apply! (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'TEXTS))) (dk-asms)) 'x)
(ass)
(qed 'texts-keys-disjoint)

(sp (make-wff '(FORALL alg (IMPLIES (IS-MESSAGE-ALGEBRA alg) (IN (KINV alg) (FUN (KEYS alg) (KEYS alg)))))))
(dk-peel!)
(mac-h 'is-message-algebra '(IS-MESSAGE-ALGEBRA alg))
(dk-split-all!)
(ass)
(qed 'kinv-in-fun)

(sp (make-wff '(FORALL alg (IMPLIES (IS-MESSAGE-ALGEBRA alg)
   (FORALL y (IMPLIES (IN y (KEYS alg)) (= ((KINV alg) ((KINV alg) y)) y)))))))
(dk-peel!)
(mac-h 'is-message-algebra '(IS-MESSAGE-ALGEBRA alg))
(dk-split-all!)
(dk-apply! (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'KINV))) (dk-asms)) 'y)
(ass)
(qed 'kinv-involution)

(sp (make-wff '(FORALL alg (IMPLIES (IS-MESSAGE-ALGEBRA alg)
   (FORALL y (FORALL z (IMPLIES (IN y (KEYS alg)) (IMPLIES (IN z (KEYS alg))
     (IMPLIES (= ((KINV alg) y) ((KINV alg) z)) (= y z))))))))))
(dk-peel!)
(fact 'kinv-involution 'alg 'y)
(fact 'kinv-involution 'alg 'z)
(subst '(= y ((KINV alg) ((KINV alg) y))))
(subst '(= ((KINV alg) y) ((KINV alg) z)))
(ass)
(qed 'kinv-injective)

;;; -----------------------------------------------------------------------
;;; 13. The subterm relation (Definition 2.11): its four clauses, minimality.

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

;; (IS-SUBTERM tt kk a b) in context: land (IN a A), (IN b A) and the universal
;; "every closed q in POWER(A x A) holds [a, b]", which is returned.
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

;; The kind of a clause of IS-SUBTERM-CLOSED, read off the pair in its final
;; conclusion (IN (LIST a X) r): X a variable is reflexivity, an ENC the
;; encryption clause, a CAT(g, h) the left or right clause according as the
;; first antecedent's pair ends in g or in h.
(define (sml-clause-kind f)
  (let loop ((f f) (vars '()))
    (if (dk-head-is? f 'FORALL)
        (loop (caddr f) (append vars (list (cadr f))))
        (let* ((ante (cadr f))
               (concl (let c ((x f)) (if (dk-head-is? x 'IMPLIES) (c (caddr x)) x)))
               (x (caddr (cadr concl))))
          (cond ((not (pair? x)) 'refl)
                ((eq? (car x) 'ENC) 'enc)
                ((equal? (caddr (cadr ante)) (cadr x)) 'cat-left)
                (else 'cat-right))))))

;; The goal (IS-SUBTERM tt kk a b) with (IN a A), (IN b A) in context.  STEP is
;; called on the lane where q is a closed relation in POWER(A x A), with the
;; four clauses of q's closedness split into the context, as (STEP q CLAUSE-OF);
;; it must close (IN [a, b] q).  PRE is run first with q (before the closedness
;; is opened: a universal that must be cited at q is cited there).
(define (sml-st-intro! tt kk a b pre step)
  (mac 'is-subterm)
  (mac 'SUBTERM-REL)
  (in-sep! (lambda () (fact 'pair-in-cartesian (sml-msgs tt kk) (sml-msgs tt kk) a b) (ass))
           (lambda ()
             (dk-peel!)
             (let* ((q (caddr (dk-goal)))
                    (closed `(IS-SUBTERM-CLOSED ,tt ,kk ,q)))
               (pre q)
               (let* ((landed (dk-landed (lambda () (mac-h 'is-subterm-closed closed))))
                      (clauses (dk-split-all!))
                      (clause-of (lambda (kind)
                                   (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL)
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

(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL g (FORALL y
   (IMPLIES (IS-SUBTERM T K a g) (IMPLIES (IN y K) (IS-SUBTERM T K a (ENC g y)))))))))))
(dk-peel!)
(let ((u (sml-st-open! 'T 'K 'a 'g)))
  (fact 'enc-in-msgs 'T 'K 'g 'y)
  (sml-st-intro! 'T 'K 'a '(ENC g y)
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'enc) 'a 'g 'y) (ass))))
(qed 'subterm-enc)

(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL g (FORALL h
   (IMPLIES (IS-SUBTERM T K a g) (IMPLIES (IN h (MSG-SET T K)) (IS-SUBTERM T K a (CAT g h)))))))))))
(dk-peel!)
(let ((u (sml-st-open! 'T 'K 'a 'g)))
  (fact 'cat-in-msgs 'T 'K 'g 'h)
  (sml-st-intro! 'T 'K 'a '(CAT g h)
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'cat-left) 'a 'g 'h) (ass))))
(qed 'subterm-cat-left)

(sp (make-wff '(FORALL T (FORALL K (FORALL a (FORALL g (FORALL h
   (IMPLIES (IS-SUBTERM T K a h) (IMPLIES (IN g (MSG-SET T K)) (IS-SUBTERM T K a (CAT g h)))))))))))
(dk-peel!)
(let ((u (sml-st-open! 'T 'K 'a 'h)))
  (fact 'cat-in-msgs 'T 'K 'g 'h)
  (sml-st-intro! 'T 'K 'a '(CAT g h)
    (lambda (q) (dk-apply! u q))
    (lambda (q clause-of) (dk-apply! (clause-of 'cat-right) 'a 'g 'h) (ass))))
(qed 'subterm-cat-right)

;;; -----------------------------------------------------------------------
;;; 14. Inversion of the subterm relation (what "the smallest relation" buys),
;;;     Proposition 2.12, transitivity.  Each is `subterm-least' at a SEP of
;;;     SUBTERM-REL by a condition on the pair, which must then be shown closed.

;; IS-SUBTERM <-> membership of the pair in SUBTERM-REL, each way, landed.
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

;; The goal (IS-SUBTERM-CLOSED tt kk RR), RR = (SEP v (SUBTERM-REL tt kk) COND):
;; unfold, and hand each clause's lane to (BODY KIND), after peeling it.
(define (sml-closed! body)
  (mac 'is-subterm-closed)
  (dk-conj-close!
    (lambda ()
      (let ((kind (sml-clause-kind (dk-goal))))
        (dk-peel!)
        (body kind)))))

;; The inversion condition on a pair (u, v), binders sig_ siy_ sih_.
(define (sml-inv tt kk u v)
  `(OR (= ,u ,v)
       (OR (FORSOME sig_ (FORSOME siy_ (AND (IN siy_ ,kk) (AND (= ,v (ENC sig_ siy_)) (IS-SUBTERM ,tt ,kk ,u sig_)))))
           (FORSOME sig_ (FORSOME sih_ (AND (= ,v (CAT sig_ sih_))
                                            (OR (IS-SUBTERM ,tt ,kk ,u sig_) (IS-SUBTERM ,tt ,kk ,u sih_))))))))
(define (sml-pair-cond p cond2)          ; exists u, v. p = [u, v] and COND2(u, v)
  `(FORSOME siu_ (FORSOME siv_ (AND (= ,p (LIST siu_ siv_)) ,(cond2 'siu_ 'siv_)))))

;; (IN [a, b] RR) in context, RR = (SEP v ST (pair-cond v COND2)): land COND2(a, b)
;; (alpha-equal to the caller's spelling) and return it.
(define (sml-pair-cond-open! rr a b cond2)
  (sep-me `(IN (LIST ,a ,b) ,rr))
  (sml-pair-cond-unpack! a b cond2))

;; The same, once the SEP membership has been opened (the pair condition, an
;; existential over [a, b], is in context).
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

;; The goal (IN [a, b] RR): the domain by IS-SUBTERM (in context, or proven by
;; THUNK-ST), the condition by witnesses a, b and COND-THUNK on COND2(a, b).
(define (sml-pair-cond-intro! tt kk a b cond-thunk)
  (sml-st-mem! tt kk a b)
  (in-sep! (lambda () (ass))
           (lambda ()
             (ew a)
             (ew b)
             (dk-each-leaf! (lambda () (di))
               (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (cond-thunk)))))))

;; The four clause lanes for a SEP RR of SUBTERM-REL by a pair condition, each
;; reduced to the one fact its pair needs: (CLOSE KIND x c PREV) runs on the
;; condition leaf of the new pair [x, c], with PREV the pair [x, prev] it was
;; built from (#f for reflexivity), IS-SUBTERM of both pairs in context.
(define (sml-closed-pairs! tt kk rr close)
  (sml-closed!
    (lambda (kind)
      (let* ((pr (cadr (dk-goal))) (x (cadr pr)) (c (caddr pr)))
        (case kind
          ((refl)
           (fact 'subterm-refl tt kk x)
           (sml-pair-cond-intro! tt kk x x (lambda () (close kind x c #f))))
          (else
           (let* ((prev (case kind ((enc cat-left) (cadr c)) (else (caddr c)))))
             (sep-me `(IN (LIST ,x ,prev) ,rr))
             (sml-st-pred! tt kk x prev)
             (fact 'subterm-in-msgs tt kk x prev)
             (dk-split-all!)
             ;; type the new right-hand side BEFORE anything is instantiated at it
             (if (eq? kind 'enc)
                 (fact 'enc-in-msgs tt kk (cadr c) (caddr c))
                 (fact 'cat-in-msgs tt kk (cadr c) (caddr c)))
             (case kind
               ((enc) (fact 'subterm-enc tt kk x (cadr c) (caddr c)))
               ((cat-left) (fact 'subterm-cat-left tt kk x (cadr c) (caddr c)))
               (else (fact 'subterm-cat-right tt kk x (cadr c) (caddr c))))
             (sml-pair-cond-intro! tt kk x c (lambda () (close kind x c prev))))))))))

(define (sml-conj-eq-ass!)
  (dk-conj-close! (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (ass)))))

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b)
    (OR (= a b)
     (OR (FORSOME g (FORSOME y (AND (IN y K) (AND (= b (ENC g y)) (IS-SUBTERM T K a g)))))
         (FORSOME g (FORSOME h (AND (= b (CAT g h)) (OR (IS-SUBTERM T K a g) (IS-SUBTERM T K a h))))))))))))))))
(dk-peel!)
(let* ((cond2 (lambda (u v) (sml-inv 'T 'K u v)))
       (rr `(SEP sip_ (SUBTERM-REL T K) ,(sml-pair-cond 'sip_ cond2))))
  (dk-have! `(IN ,rr (POWER ,(sml-box 'T 'K))) (lambda () (sml-subrel-power! 'T 'K rr)))
  (dk-have! `(IS-SUBTERM-CLOSED T K ,rr)
    (lambda ()
      (sml-closed-pairs! 'T 'K rr
        (lambda (kind x c prev)
          (case kind
            ((refl) (oi-l) (rfl))
            ((enc) (oi-r) (oi-l) (ew (cadr c)) (ew (caddr c)) (sml-conj-eq-ass!))
            (else (oi-r) (oi-r) (ew (cadr c)) (ew (caddr c))
                  (dk-each-leaf! (lambda () (di))
                    (lambda ()
                      (cond ((dk-head-is? (dk-goal) '=) (rfl))
                            ((eq? kind 'cat-left) (oi-l) (ass))
                            (else (oi-r) (ass)))))))))))
  (fact 'subterm-least 'T 'K rr)
  (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                              (not (dk-contains? f 'IS-SUBTERM-CLOSED))))
                             (dk-asms))
                 (error "subterm-cases: subterm-least did not detach"))
             'a 'b)
  (sml-pair-cond-open! rr 'a 'b cond2)
  (ass))
(qed 'subterm-cases)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (FORALL c
    (IMPLIES (IS-SUBTERM T K a b) (IMPLIES (IS-SUBTERM T K b c) (IS-SUBTERM T K a c))))))))))))
(dk-peel!)
(let* ((cond2 (lambda (u v) `(FORALL sia_ (IMPLIES (IS-SUBTERM T K sia_ ,u) (IS-SUBTERM T K sia_ ,v)))))
       (rr `(SEP sip_ (SUBTERM-REL T K) ,(sml-pair-cond 'sip_ cond2))))
  (dk-have! `(IN ,rr (POWER ,(sml-box 'T 'K))) (lambda () (sml-subrel-power! 'T 'K rr)))
  (dk-have! `(IS-SUBTERM-CLOSED T K ,rr)
    (lambda ()
      (sml-closed-pairs! 'T 'K rr
        (lambda (kind x c prev)
          (if (eq? kind 'refl)
              (begin (dk-peel!) (ass))
              (let ((ih (sml-pair-cond-unpack! x prev cond2)))
                (dk-peel!)
                (let ((a1 (list-ref (dk-goal) 3)))       ; (IS-SUBTERM T K a1 c)
                  (dk-apply! ih a1)
                  (case kind
                    ((enc) (fact 'subterm-enc 'T 'K a1 (cadr c) (caddr c)))
                    ((cat-left) (fact 'subterm-cat-left 'T 'K a1 (cadr c) (caddr c)))
                    (else (fact 'subterm-cat-right 'T 'K a1 (cadr c) (caddr c))))
                  (ass))))))))
  (fact 'subterm-least 'T 'K rr)
  (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                              (not (dk-contains? f 'IS-SUBTERM-CLOSED))))
                             (dk-asms))
                 (error "subterm-trans: subterm-least did not detach"))
             'b 'c)
  (dk-apply! (sml-pair-cond-open! rr 'b 'c cond2) 'a)
  (ass))
(qed 'subterm-trans)

;; The disjunction subterm-cases lands for the pair (a, b), split three ways:
;; (ON-EQ) with (= a b) in context, (ON-ENC g y) and (ON-CAT g h) with the
;; witnesses skolemised and their conjuncts split into the context.
(define (sml-subterm-cases! tt kk a b on-eq on-enc on-cat)
  (let ((o (dk-cite! 'subterm-cases tt kk a b)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? `(= ,a ,b))
            (on-eq)
            (let ((o2 (or (find-first (lambda (f) (and (dk-head-is? f 'OR) (dk-head-is? (cadr f) 'FORSOME)
                                                       (dk-contains? f b)))
                                      (dk-asms))
                          (error "sml-subterm-cases!: no second disjunction"))))
              (dk-each-leaf! (lambda () (ai o2))
                (lambda ()
                  (let* ((ex (find-first (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f b)
                                                          (not (dk-head-is? (caddr f) 'OR))))
                                         (dk-asms)))
                         (vs (sml-unpack! ex))
                         (encp (begin (dk-split-all!)
                                      (dk-asm? `(= ,b (ENC ,(car vs) ,(cadr vs)))))))
                    (if encp (on-enc (car vs) (cadr vs)) (on-cat (car vs) (cadr vs))))))))))))

;; (= y x) in context and x TYPED: land (= x y) (rewrite x to y, close by rfl).
(define (sml-flip! x y)
  (dk-have! `(= ,x ,y) (lambda () (subst `(= ,x ,y)) (rfl))))

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL c (IMPLIES (IN c (UNION T K))
    (IMPLIES (IS-SUBTERM T K a (ATOM c)) (= a (ATOM c))))))))))))
(dk-peel!)
(fact 'atom-in-msgs 'T 'K 'c)
(sml-subterm-cases! 'T 'K 'a '(ATOM c)
  (lambda () (ass))
  (lambda (g y) (fact 'atom-ne-enc 'c g y) (ai `(NOT (= (ATOM c) (ENC ,g ,y)))))
  (lambda (g h) (fact 'atom-ne-cat 'c g h) (ai `(NOT (= (ATOM c) (CAT ,g ,h))))))
(qed 'subterm-of-atom)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL g (FORALL y (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
    (IMPLIES (IS-SUBTERM T K a (ENC g y)) (OR (= a (ENC g y)) (IS-SUBTERM T K a g))))))))))))))
(dk-peel!)
(fact 'enc-in-msgs 'T 'K 'g 'y)
(sml-subterm-cases! 'T 'K 'a '(ENC g y)
  (lambda () (oi-l) (ass))
  (lambda (g1 y1)
    (fact 'enc-injective 'g 'y g1 y1)
    (dk-split-all!)
    (oi-r)
    (subst `(= g ,g1))
    (ass))
  (lambda (g1 h1)
    (sml-flip! `(CAT ,g1 ,h1) '(ENC g y))
    (fact 'cat-ne-enc g1 h1 'g 'y)
    (ai `(NOT (= (CAT ,g1 ,h1) (ENC g y))))))
(qed 'subterm-of-enc)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL g (FORALL h (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN h (MSG-SET T K))
    (IMPLIES (IS-SUBTERM T K a (CAT g h))
      (OR (= a (CAT g h)) (OR (IS-SUBTERM T K a g) (IS-SUBTERM T K a h)))))))))))))))
(dk-peel!)
(fact 'cat-in-msgs 'T 'K 'g 'h)
(sml-subterm-cases! 'T 'K 'a '(CAT g h)
  (lambda () (oi-l) (ass))
  (lambda (g1 y1) (fact 'cat-ne-enc 'g 'h g1 y1) (ai `(NOT (= (CAT g h) (ENC ,g1 ,y1)))))
  (lambda (g1 h1)
    (fact 'cat-injective 'g 'h g1 h1)
    (dk-split-all!)
    (oi-r)
    (subst `(= g ,g1))
    (subst `(= h ,h1))
    (ass)))
(qed 'subterm-of-cat)

;;; PROPOSITION 2.12: K /= K' and {h'}_K' @ {h}_K imply {h'}_K' @ h.  The paper's
;;; K, K', h, h' are written y, y2, h, h2; the typings h, h2 in A and y, y2 in K are
;;; the paper's implicit ones (its terms range over A, its keys over K).
(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL h (FORALL h2 (FORALL y (FORALL y2
    (IMPLIES (IN h (MSG-SET T K)) (IMPLIES (IN h2 (MSG-SET T K)) (IMPLIES (IN y K) (IMPLIES (IN y2 K)
      (IMPLIES (NOT (= y y2))
        (IMPLIES (IS-SUBTERM T K (ENC h2 y2) (ENC h y)) (IS-SUBTERM T K (ENC h2 y2) h)))))))))))))))))
(dk-peel!)
(fact 'enc-in-msgs 'T 'K 'h 'y)
(fact 'enc-in-msgs 'T 'K 'h2 'y2)
(sml-subterm-cases! 'T 'K '(ENC h2 y2) '(ENC h y)
  (lambda ()
    (fact 'enc-injective 'h2 'y2 'h 'y)
    (dk-split-all!)
    (dk-have! '(= y y2) (lambda () (subst '(= y2 y)) (rfl)))
    (ai '(NOT (= y y2))))
  (lambda (g1 y1)
    (fact 'enc-injective 'h 'y g1 y1)
    (dk-split-all!)
    (subst `(= h ,g1))
    (ass))
  (lambda (g1 h1)
    (sml-flip! `(CAT ,g1 ,h1) '(ENC h y))
    (fact 'cat-ne-enc g1 h1 'h 'y)
    (ai `(NOT (= (CAT ,g1 ,h1) (ENC h y))))))
(qed 'subterm-enc-other-key)

;;; -----------------------------------------------------------------------
;;; 15. THE RANK: the least stage holding a message.  `iota-d' grants the
;;;     description's property once existence (nn-least-element on the set of
;;;     stage indices holding m) and uniqueness (nn-le-antisym) are shown.

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
          (else #f))))
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

;; msg-stage-succ-cases for m at stage succ(n), split: (ON-KEEP) with m in stage n;
;; (ON-CAT g h) / (ON-ENC g y) with the witnesses skolemised, their stage
;; typings and the equation m = CAT(g, h) / m = ENC(g, y) in context.
(define (sml-succ-cases! tt kk n m on-keep on-cat on-enc)
  (let ((o (dk-cite! 'msg-stage-succ-cases tt kk n m)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? `(IN ,m (MSG-STAGE ,tt ,kk ,n)))
            (on-keep)
            (let ((o2 (or (find-first (lambda (f) (and (dk-head-is? f 'OR) (dk-head-is? (cadr f) 'FORSOME)
                                                       (dk-contains? f m)))
                                      (dk-asms))
                          (error "sml-succ-cases!: no second disjunction"))))
              (dk-each-leaf! (lambda () (ai o2))
                (lambda ()
                  (let* ((ex (find-first (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f m)
                                                          (not (dk-head-is? (caddr f) 'OR))))
                                         (dk-asms)))
                         (vs (sml-unpack! ex)))
                    (dk-split-all!)
                    (if (dk-asm? `(= ,m (CAT ,(car vs) ,(cadr vs))))
                        (on-cat (car vs) (cadr vs))
                        (on-enc (car vs) (cadr vs))))))))))))

;; The stage index of a member, read off (IN x (MSG-STAGE tt kk n)) in context.
(define (sml-stage-of x)
  (let ((f (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) x)
                                        (dk-head-is? (caddr f) 'MSG-STAGE)))
                       (dk-asms))))
    (and f (cadddr (caddr f)))))

;;; The component of an encryption or a concatenation sits at a strictly earlier
;;; stage.  Induction on the stage index, outermost.

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (FORALL T (FORALL K (FORALL g (FORALL y
   (IMPLIES (IN (ENC g y) (MSG-STAGE T K n))
     (FORSOME j (AND (IN j NN) (AND (<= (succ j) n) (IN g (MSG-STAGE T K j))))))))))))))
(define sml-cases3 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases3))
(dk-peel!)
(let* ((a (dk-skolem! (dk-cite! 'msg-stage-zero-cases 'T 'K '(ENC g y)))))
  (sml-flip! `(ATOM ,a) '(ENC g y))
  (fact 'atom-ne-enc a 'g 'y)
  (ai `(NOT (= (ATOM ,a) (ENC g y)))))
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases3))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (m (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (cadr f) 'ENC))) landed)))
       (gg (cadr m)) (yy (caddr m))
       (stg (caddr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) m))) landed)))
       (tt (cadr stg)) (kk (caddr stg)) (n (cadr (cadddr stg))))
  (sml-succ-cases! tt kk n m
    (lambda ()
      (let ((j (dk-skolem! (dk-apply! ih tt kk gg yy))))
        (dk-split-all!)
        (ew j)
        (dk-conj-close!
          (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn! `(<= (succ ,j) ,n)) (ass))))))
    (lambda (g1 h1)
      (sml-flip! `(CAT ,g1 ,h1) m)
      (fact 'cat-ne-enc g1 h1 gg yy)
      (ai `(NOT (= (CAT ,g1 ,h1) ,m))))
    (lambda (g1 y1)
      (fact 'enc-injective gg yy g1 y1)
      (dk-split-all!)
      (ew n)
      (dk-conj-close!
        (lambda ()
          (cond ((dk-head-is? (dk-goal) '<=) (dk-nn!))
                ((equal? (cadr (dk-goal)) gg) (subst `(= ,gg ,g1)) (ass))
                (else (ass))))))))
(qed 'msg-stage-enc-inv)

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (FORALL T (FORALL K (FORALL g (FORALL h
   (IMPLIES (IN (CAT g h) (MSG-STAGE T K n))
     (FORSOME j (AND (IN j NN) (AND (<= (succ j) n)
                                    (AND (IN g (MSG-STAGE T K j)) (IN h (MSG-STAGE T K j)))))))))))))))
(define sml-cases4 (dk-opened (lambda () (ni))))
(dk-focus! (find-first (lambda (l) (not (sml-step-case? (dk-goal-of l)))) sml-cases4))
(dk-peel!)
(let* ((a (dk-skolem! (dk-cite! 'msg-stage-zero-cases 'T 'K '(CAT g h)))))
  (sml-flip! `(ATOM ,a) '(CAT g h))
  (fact 'atom-ne-cat a 'g 'h)
  (ai `(NOT (= (ATOM ,a) (CAT g h)))))
(dk-focus! (find-first (lambda (l) (sml-step-case? (dk-goal-of l))) sml-cases4))
(let* ((landed (dk-peel!))
       (ih (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed))
       (m (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (cadr f) 'CAT))) landed)))
       (gg (cadr m)) (hh (caddr m))
       (stg (caddr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) m))) landed)))
       (tt (cadr stg)) (kk (caddr stg)) (n (cadr (cadddr stg))))
  (sml-succ-cases! tt kk n m
    (lambda ()
      (let ((j (dk-skolem! (dk-apply! ih tt kk gg hh))))
        (dk-split-all!)
        (ew j)
        (dk-conj-close!
          (lambda () (if (dk-head-is? (dk-goal) '<=) (dk-nn! `(<= (succ ,j) ,n)) (ass))))))
    (lambda (g1 h1)
      (fact 'cat-injective gg hh g1 h1)
      (dk-split-all!)
      (ew n)
      (dk-conj-close!
        (lambda ()
          (cond ((dk-head-is? (dk-goal) '<=) (dk-nn!))
                ((equal? (cadr (dk-goal)) gg) (subst `(= ,gg ,g1)) (ass))
                ((equal? (cadr (dk-goal)) hh) (subst `(= ,hh ,h1)) (ass))
                (else (ass))))))
    (lambda (g1 y1)
      (fact 'cat-ne-enc gg hh g1 y1)
      (ai `(NOT (= ,m (ENC ,g1 ,y1)))))))
(qed 'msg-stage-cat-inv)

;; rank-prop at the TYPED message x: land (IN rank NN), (IN x stage(rank)) and the
;; minimality universal; return the rank term.
(define (sml-rank! tt kk x)
  (fact 'msg-rank-prop tt kk x)
  (dk-split-all!)
  `(MSG-RANK ,tt ,kk ,x))
(define (sml-rank-min x)
  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (sml-has-le? f `(MSG-RANK T K ,x)))) (dk-asms))
      (error "sml-rank-min: no minimality for" x)))

(sp (make-wff '(FORALL T (FORALL K (FORALL a
   (IMPLIES (IN a (UNION T K)) (= (MSG-RANK T K (ATOM a)) 0)))))))
(dk-peel!)
(fact 'atom-in-msgs 'T 'K 'a)
(fact 'msg-stage-atom 'T 'K 'a)
(fact 'nn-zero-in)
(let ((r (sml-rank! 'T 'K '(ATOM a))))
  (dk-apply! (sml-rank-min '(ATOM a)) 0)
  (dk-nn! `(<= ,r 0)))
(qed 'msg-rank-atom)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (FORALL y
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN y K)
     (<= (succ (MSG-RANK T K g)) (MSG-RANK T K (ENC g y)))))))))))
(dk-peel!)
(fact 'enc-in-msgs 'T 'K 'g 'y)
(let* ((re (sml-rank! 'T 'K '(ENC g y)))
       (rg (sml-rank! 'T 'K 'g))
       (j (dk-skolem! (dk-cite! 'msg-stage-enc-inv re 'T 'K 'g 'y))))
  (dk-split-all!)
  (dk-apply! (sml-rank-min 'g) j)
  (dk-nn! `(<= ,rg ,j) `(<= (succ ,j) ,re)))
(qed 'msg-rank-enc)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (FORALL h
   (IMPLIES (IN g (MSG-SET T K)) (IMPLIES (IN h (MSG-SET T K))
     (AND (<= (succ (MSG-RANK T K g)) (MSG-RANK T K (CAT g h)))
          (<= (succ (MSG-RANK T K h)) (MSG-RANK T K (CAT g h))))))))))))
(dk-peel!)
(fact 'cat-in-msgs 'T 'K 'g 'h)
(let* ((rc (sml-rank! 'T 'K '(CAT g h)))
       (rg (sml-rank! 'T 'K 'g))
       (rh (sml-rank! 'T 'K 'h))
       (j (dk-skolem! (dk-cite! 'msg-stage-cat-inv rc 'T 'K 'g 'h))))
  (dk-split-all!)
  (dk-apply! (sml-rank-min 'g) j)
  (dk-apply! (sml-rank-min 'h) j)
  (dk-conj-close!
    (lambda ()
      (if (dk-contains? (dk-goal) rg)
          (dk-nn! `(<= ,rg ,j) `(<= (succ ,j) ,rc))
          (dk-nn! `(<= ,rh ,j) `(<= (succ ,j) ,rc))))))
(qed 'msg-rank-cat)

;;; -----------------------------------------------------------------------
;;; 16. A proper subterm has a strictly smaller rank; so the subterm relation
;;;     is ANTISYMMETRIC, a partial order (reflexive: subterm-refl; transitive:
;;;     subterm-trans).  The paper uses this without stating it.

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b)
    (OR (= a b) (<= (succ (MSG-RANK T K a)) (MSG-RANK T K b))))))))))))
(dk-peel!)
(let* ((cond2 (lambda (u v) `(OR (= ,u ,v) (<= (succ (MSG-RANK T K ,u)) (MSG-RANK T K ,v)))))
       (rr `(SEP sip_ (SUBTERM-REL T K) ,(sml-pair-cond 'sip_ cond2))))
  (dk-have! `(IN ,rr (POWER ,(sml-box 'T 'K))) (lambda () (sml-subrel-power! 'T 'K rr)))
  (dk-have! `(IS-SUBTERM-CLOSED T K ,rr)
    (lambda ()
      (sml-closed-pairs! 'T 'K rr
        (lambda (kind x c prev)
          (if (eq? kind 'refl)
              (begin (oi-l) (rfl))
              (let* ((ih (sml-pair-cond-unpack! x prev cond2))
                     ;; the step's own rank fact: rank(prev) < rank(c)
                     (step (lambda ()
                             (case kind
                               ((enc) (fact 'msg-rank-enc 'T 'K prev (caddr c)))
                               (else (fact 'msg-rank-cat 'T 'K (cadr c) (caddr c))))
                             (dk-split-all!))))
                (dk-each-leaf! (lambda () (ai ih))
                  (lambda ()
                    (oi-r)
                    (step)
                    (if (dk-asm? `(= ,x ,prev))
                        (begin (subst `(= ,x ,prev)) (ass))
                        (let ((rx (sml-rank! 'T 'K x)) (rp (sml-rank! 'T 'K prev)) (rc (sml-rank! 'T 'K c)))
                          (dk-nn! `(<= (succ ,rx) ,rp) `(<= (succ ,rp) ,rc))))))))))))
  (fact 'subterm-least 'T 'K rr)
  (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                              (not (dk-contains? f 'IS-SUBTERM-CLOSED))))
                             (dk-asms))
                 (error "subterm-rank: subterm-least did not detach"))
             'a 'b)
  (sml-pair-cond-open! rr 'a 'b cond2)
  (ass))
(qed 'subterm-rank)

(sp (make-wff '(FORALL T (FORALL K (IMPLIES (IN T SET) (IMPLIES (IN K SET)
  (FORALL a (FORALL b (IMPLIES (IS-SUBTERM T K a b) (IMPLIES (IS-SUBTERM T K b a) (= a b)))))))))))
(dk-peel!)
(fact 'subterm-in-msgs 'T 'K 'a 'b)
(dk-split-all!)
(let ((o1 (dk-cite! 'subterm-rank 'T 'K 'a 'b))
      (o2 (dk-cite! 'subterm-rank 'T 'K 'b 'a)))
  (dk-each-leaf! (lambda () (ai o1))
    (lambda ()
      (if (dk-asm? '(= a b))
          (ass)
          (dk-each-leaf! (lambda () (ai o2))
            (lambda ()
              (if (dk-asm? '(= b a))
                  (sml-flip! 'a 'b)
                  (let ((ra (sml-rank! 'T 'K 'a)) (rb (sml-rank! 'T 'K 'b)))
                    (dk-have! '(< 0 0)
                      (lambda () (dk-nn! `(<= (succ ,ra) ,rb) `(<= (succ ,rb) ,ra))))
                    (fact 'rr-zero-in)
                    (ai (dk-cite! 'rr-lt-irrefl 0))))))))))
(qed 'subterm-antisym)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing))
          '(atom-unfold cat-unfold enc-unfold pair-self-member pair-self-eq msg-set-unfold
            subterm-rel-unfold pair-in-cartesian-parts cartesian3-set))
(for-each (lambda (n) (topic! n 'constructions))
          '(atom-ne-cat atom-ne-enc cat-ne-enc atom-injective cat-injective enc-injective
            msg-stage-atom msg-stage-keep msg-stage-cat msg-stage-enc msg-stage-zero-cases
            msg-stage-succ-cases msg-stage-add msg-set-intro msg-set-elim atom-in-msgs cat-in-msgs
            enc-in-msgs msg-induction msg-cases msg-stage-set msg-set-is-set message-algebra-msgs
            texts-keys-disjoint kinv-in-fun kinv-involution kinv-injective subterm-in-msgs
            subterm-least subterm-refl subterm-enc subterm-cat-left subterm-cat-right subterm-cases
            subterm-trans subterm-of-atom subterm-of-enc subterm-of-cat subterm-enc-other-key
            msg-rank-prop msg-stage-enc-inv msg-stage-cat-inv msg-rank-atom msg-rank-enc msg-rank-cat
            subterm-rank subterm-antisym))
