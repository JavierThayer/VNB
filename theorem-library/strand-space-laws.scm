;;; strand-space-laws.scm -- STRAND SPACES, NODES, BUNDLES, CAUSAL PRECEDENCE: the laws, and the
;;; paper's Lemmas 2.7, 2.8, 2.9 on the user's model.
;;; (~/notes/notes-60.txt; the definitions are structure-library/strand-spaces.scm; the paper is
;;;  Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, sections 2.2-2.4.)
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06.  Helper prefix: ssl-.  S-2b (the same day)
;;; added the key parameter of the messages (MSG-SET(T, K), DIRECTED(T, K), STRANDS(T, K),
;;; IS-SUBTERM(T, K, a, b)) and the four key laws; nothing else changed (S-2's version:
;;; archive/2026-10-06/s2b/strand-space-laws.scm).
;;;
;;; Every theorem bills `modulo 0'; the oracles are `arith' (ground numerals) and `ineq' (NN linear
;;; arithmetic through dk-nn!).  Nothing is asserted, stamped or warranted.
;;;
;;; WHAT IS PROVEN (in this order)
;;;  0. The unfold equations of the functoids (mac-h cannot unfold a functoid in a hypothesis).
;;;  1. NODES.  strand-space-parts, keys-in-tokens, kinv-in-fun, kinv-involution, kinv-injective
;;;     (the keys, S-2b), strand-at-id, node-parts, node-intro, node-pair-injective,
;;;     node-ext, directed-parts, node-step-in-directed, node-content-in-msgs,
;;;     node-dir-cases, sent-ne-received, node-sent-or-received, node-not-sent-and-received,
;;;     node-content-eq (a node's content and direction read off its strand entry).
;;;  2. THE RELATIONS.  ssb-irreflexive, ssb-transitive, ssu-of-ssb, ssu-refl, ssu-cases (==>= is
;;;     ==> u identity, both directions), sends-to-dirs.
;;;  3. BUNDLES.  The law projections (bundle-space ... bundle-acyclic), pair-in-power-box,
;;;     bundle-send-nodes, bundle-ssb-closed (the ONE-CLAUSE closure under ==>).
;;;  4. PRECEDES-STRICT on loose data: ps-in-box, ps-least (minimality), ps-send, ps-ssb (the
;;;     edges are in), ps-trans; ps-last-step (INVERSION: a pair is reached by a last edge);
;;;     on bundles: precedes-strict-trans, precedes-strict-irreflexive, bundle-send-precedes,
;;;     bundle-ssb-precedes; PRECEDES: precedes-intro-strict, precedes-refl, precedes-elim.
;;;  5. LEMMA 2.7.  precedes-trans, precedes-antisym, precedes-set, precedes-partial-order
;;;     (IS-PARTIAL-ORDER of structure-library/order-zorn.scm), finite-strict-minimal (any
;;;     transitive irreflexive relation: every nonempty finite set has a minimal member, by
;;;     finite-set-induction), bundle-minimal (every nonempty set of nodes of a bundle has a
;;;     PRECEDES-STRICT-minimal member, the witness explicit), bundle-minimal-precedes (the same
;;;     with the paper's <=: no OTHER member precedes it).
;;;  6. LEMMA 2.8 (bundle-minimal-sent), the origination facts (originates-intro,
;;;     originates-elim, originates-sent, originates-no-earlier, originates-unique), LEMMA 2.9
;;;     (bundle-minimal-originates).
;;;
;;; LOAD WINDOW: after strand-messages-laws (subterm laws, pair-self-*, pair-in-cartesian-parts),
;;; structure-library/strand-spaces, structure-library/order-zorn (IS-PARTIAL-ORDER),
;;; theorem-library/rake-card-star-laws (finite-set-induction), card-subset-nn, subset-lemmas,
;;; nn-pos-of-nonzero, nn-order-ord, rr-order-basics, axioms.scm (fun-apply-type).

;;; -----------------------------------------------------------------------
;;; helpers (prefix ssl-)

(define (ssl-keep-prop! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply dk-only! fs)
    (if (not (sequent-node-grounded? node)) (prop))))

;; The conjunction of FS (right-nested), from the context.
(define (ssl-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(ssl-and (cdr fs)))))
(define (ssl-have-and! . fs)
  (let ((c (ssl-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (ass)))))
    c))

;; (IN x F) in context and (== F BODY) landed as EQN: land and return (IN x BODY).
(define (ssl-open-in! mem eqn)
  (let ((claim `(IN ,(cadr mem) ,(caddr eqn))))
    (dk-have! claim (lambda () (subst `(= ,(caddr eqn) ,(cadr eqn))) (ass)))
    claim))

;; (IN x (CARTESIAN C1 ... Cn)) in context: land the existential chain (fixed binders).
(define (ssl-cart-chain x classes)
  (let nest ((i 1) (cs classes) (vars '()))
    (if (null? cs)
        `(= ,x (LIST ,@(reverse vars)))
        (let ((v (string->symbol (string-append "cdv" (number->string i) "_"))))
          `(FORSOME ,v (AND (IN ,v ,(car cs)) ,(nest (+ i 1) (cdr cs) (cons v vars))))))))
(define (ssl-cart-open! mem)
  (let* ((ex  (ssl-cart-chain (cadr mem) (cdr (caddr mem))))
         (imp `(IMPLIES ,mem ,ex)))
    (dk-have! imp (lambda () (mac 'cartesian-decompose) (di) (ass)))
    (detach! imp)
    (or (dk-ctx-form ex) (error "ssl-cart-open!: the chain did not land" (expression->string ex)))))
;; With a COUNT, stop after that many binders (a FORSOME inside the body is left alone).
(define (ssl-unpack! ex . count)
  (let loop ((ex ex) (acc '()) (k (if (pair? count) (car count) 1000)))
    (let* ((before (dk-asms))
           (v (dk-skolem! ex))
           (new (filter (lambda (f) (not (member f before))) (dk-asms)))
           (next (find-first (lambda (f) (dk-head-is? f 'FORSOME)) new)))
      (if (and next (> k 1)) (loop next (cons v acc) (- k 1)) (reverse (cons v acc))))))

;; Project a structure predicate HYP (e.g. (IS-BUNDLE c)) and close the focus goal from its
;; conjuncts (the goal is one conjunct, or an AND of conjuncts).
(define (ssl-proj! pred hyp)
  (mac-h pred hyp)
  (dk-split-all!)
  (if (dk-head-is? (dk-goal) 'AND) (dk-conj-close! (lambda () (ass))) (ass)))

;; Land the claim CLAIM, a projection of the predicate hypothesis HYP, on a lane (HYP survives).
(define (ssl-project! pred hyp claim)
  (dk-have! claim (lambda () (ssl-proj! pred hyp)))
  claim)

;;; -----------------------------------------------------------------------
;;; 0. Unfold equations.

(sp (make-wff '(FORALL spa (== (NODES spa)
   (SEP ssn_ (CARTESIAN NN (IDS spa))
        (AND (<= 1 (NTH 1 ssn_)) (<= (NTH 1 ssn_) (LENGTH ((STRAND-MAP spa) (NTH 2 ssn_))))))))))
(di) (mac 'NODES) (qrfl)
(qed 'nodes-unfold)

(sp (make-wff '(FORALL spa (FORALL n (== (NODE-CONTENT spa n)
   (NTH 2 (NTH (NTH 1 n) ((STRAND-MAP spa) (NTH 2 n)))))))))
(di) (mac 'NODE-CONTENT) (qrfl)
(qed 'node-content-unfold)

(sp (make-wff '(FORALL spa (FORALL n (== (NODE-DIR spa n)
   (NTH 1 (NTH (NTH 1 n) ((STRAND-MAP spa) (NTH 2 n)))))))))
(di) (mac 'NODE-DIR) (qrfl)
(qed 'node-dir-unfold)

(sp (make-wff '(FORALL T (FORALL K (== (DIRECTED T K) (CARTESIAN (PAIR SENT RECEIVED) (MSG-SET T K)))))))
(di) (mac 'DIRECTED) (qrfl)
(qed 'directed-unfold)

(sp (make-wff '(FORALL T (FORALL K (== (STRANDS T K) (TUPLES (DIRECTED T K)))))))
(di) (mac 'STRANDS) (qrfl)
(qed 'strands-unfold)

(sp (make-wff '(FORALL n (AND (== (INDEX-OF n) (NTH 1 n)) (== (ID-OF n) (NTH 2 n))))))
(di) (dk-conj-close! (lambda () (if (dk-contains? (dk-goal) 'INDEX-OF) (mac 'INDEX-OF) (mac 'ID-OF)) (qrfl)))
(qed 'index-id-unfold)

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (== (PREC-STRICT spa ND ED)
   (SEP ssp_ (CARTESIAN ND ND)
        (FORALL ssq_ (IMPLIES (IN ssq_ (POWER (CARTESIAN ND ND)))
                              (IMPLIES (IS-PREC-CLOSED spa ND ED ssq_) (IN ssp_ ssq_)))))))))))
(di) (mac 'PREC-STRICT) (qrfl)
(qed 'prec-strict-unfold)

(sp (make-wff '(FORALL c (== (PRECEDES-STRICT c) (PREC-STRICT (BSPACE c) (BNODES c) (BSEND c))))))
(di) (mac 'PRECEDES-STRICT) (qrfl)
(qed 'precedes-strict-unfold)

(sp (make-wff '(FORALL c (== (PRECEDES c)
   (UNION (PRECEDES-STRICT c)
          (SEP ssp_ (CARTESIAN (BNODES c) (BNODES c)) (= (NTH 1 ssp_) (NTH 2 ssp_))))))))
(di) (mac 'PRECEDES) (qrfl)
(qed 'precedes-unfold)

;;; -----------------------------------------------------------------------
;;; 1. The strand space and its nodes.

(sp (make-wff '(FORALL spa (IMPLIES (IS-STRAND-SPACE spa)
   (AND (IS-TOKEN-SET (TOKENS spa))
        (AND (IN (TOKENS spa) SET)
             (AND (IN (IDS spa) SET)
                  (AND (IN (KEYS spa) SET)
                       (IN (STRAND-MAP spa) (FUN (IDS spa) (STRANDS (TOKENS spa) (KEYS spa))))))))))))
(di) (di)
(ssl-proj! 'is-strand-space '(IS-STRAND-SPACE spa))
(qed 'strand-space-parts)

;;; The keys (S-2b): a key is a token; KINV is an involution of KEYS, hence injective.
(sp (make-wff '(FORALL spa (IMPLIES (IS-STRAND-SPACE spa)
   (FORALL x (IMPLIES (IN x (KEYS spa)) (IN x (TOKENS spa))))))))
(dk-peel!)
(mac-h 'is-strand-space '(IS-STRAND-SPACE spa))
(dk-split-all!)
(dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'TOKENS) (not (dk-contains? f 'KINV))))
                    "the key law")
           'x)
(ass)
(qed 'keys-in-tokens)

(sp (make-wff '(FORALL spa (IMPLIES (IS-STRAND-SPACE spa) (IN (KINV spa) (FUN (KEYS spa) (KEYS spa)))))))
(di) (di)
(ssl-proj! 'is-strand-space '(IS-STRAND-SPACE spa))
(qed 'kinv-in-fun)

(sp (make-wff '(FORALL spa (IMPLIES (IS-STRAND-SPACE spa)
   (FORALL y (IMPLIES (IN y (KEYS spa)) (= ((KINV spa) ((KINV spa) y)) y)))))))
(dk-peel!)
(mac-h 'is-strand-space '(IS-STRAND-SPACE spa))
(dk-split-all!)
(dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'KINV))) "the involution law") 'y)
(ass)
(qed 'kinv-involution)

(sp (make-wff '(FORALL spa (IMPLIES (IS-STRAND-SPACE spa)
   (FORALL y (FORALL z (IMPLIES (IN y (KEYS spa)) (IMPLIES (IN z (KEYS spa))
     (IMPLIES (= ((KINV spa) y) ((KINV spa) z)) (= y z))))))))))
(dk-peel!)
(fact 'kinv-involution 'spa 'y)
(fact 'kinv-involution 'spa 'z)
(subst '(= y ((KINV spa) ((KINV spa) y))))
(subst '(= ((KINV spa) y) ((KINV spa) z)))
(ass)
(qed 'kinv-injective)

;; The parts of a strand space SPA in context, landed (on a lane: the hypothesis survives).
(define (ssl-space! spa)
  (let ((f (dk-cite! 'strand-space-parts spa)))
    (dk-split-all!)
    f))

(sp (make-wff '(FORALL spa (FORALL a (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN a (IDS spa))
   (IN ((STRAND-MAP spa) a) (TUPLES (DIRECTED (TOKENS spa) (KEYS spa))))))))))
(dk-peel!)
(ssl-space! 'spa)
(ssl-have-and! '(IN (STRAND-MAP spa) (FUN (IDS spa) (STRANDS (TOKENS spa) (KEYS spa)))) '(IN a (IDS spa)))
(fact 'fun-apply-type '(STRAND-MAP spa) '(IDS spa) '(STRANDS (TOKENS spa) (KEYS spa)) 'a)
(fact 'strands-unfold '(TOKENS spa) '(KEYS spa))
(subst '(= (TUPLES (DIRECTED (TOKENS spa) (KEYS spa))) (STRANDS (TOKENS spa) (KEYS spa))))
(ass)
(qed 'strand-at-id)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IN n (NODES spa))
   (AND (IN (NTH 1 n) NN)
        (AND (IN (NTH 2 n) (IDS spa))
             (AND (<= 1 (NTH 1 n))
                  (AND (<= (NTH 1 n) (LENGTH ((STRAND-MAP spa) (NTH 2 n))))
                       (= n (LIST (NTH 1 n) (NTH 2 n))))))))))))
(dk-peel!)
(let* ((sepm (ssl-open-in! '(IN n (NODES spa)) (dk-cite! 'nodes-unfold 'spa))))
  (sep-me sepm)
  (dk-split-all!)
  (let* ((vs (ssl-unpack! (ssl-cart-open! '(IN n (CARTESIAN NN (IDS spa))))))
         (k (car vs)) (a (cadr vs)))
    (dk-have! `(= (NTH 1 n) ,k) (lambda () (subst `(= n (LIST ,k ,a))) (nth-r) (rfl)))
    (dk-have! `(= (NTH 2 n) ,a) (lambda () (subst `(= n (LIST ,k ,a))) (nth-r) (rfl)))
    (dk-conj-close!
      (lambda ()
        (cond ((dk-asm? (dk-goal)) (ass))
              (#t                                  ; a typing, or n = [NTH 1 n, NTH 2 n]
               (if (dk-contains? (dk-goal) '(NTH 1 n)) (subst `(= (NTH 1 n) ,k)))
               (if (dk-contains? (dk-goal) '(NTH 2 n)) (subst `(= (NTH 2 n) ,a)))
               (ass)))))))
(qed 'node-parts)

;; The parts of the node N of SPA (N in NODES(SPA) in context), landed.
(define (ssl-node! spa n)
  (fact 'node-parts spa n)
  (dk-split-all!))

(sp (make-wff '(FORALL spa (FORALL k (FORALL a (IMPLIES (IN k NN) (IMPLIES (IN a (IDS spa))
   (IMPLIES (<= 1 k) (IMPLIES (<= k (LENGTH ((STRAND-MAP spa) a))) (IN (LIST k a) (NODES spa)))))))))))
(dk-peel!)
(mac 'NODES)
(in-sep! (lambda () (fact 'pair-in-cartesian 'NN '(IDS spa) 'k 'a) (ass))
         (lambda () (nth-r) (dk-conj-close! (lambda () (ass)))))
(qed 'node-intro)

;;; A node has one index and one identifier: [k, a] = [j, b] gives k = j and a = b.
(define (ssl-component! l1 l2 i)
  (let* ((x (list-ref l1 i)) (y (list-ref l2 i)))
    (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
    (subst `(= ,y (NTH ,i ,l2)))
    (subst `(= ,l2 ,l1))
    (nth-r)
    (rfl)))

(sp (make-wff '(FORALL k (FORALL a (FORALL j (FORALL b
   (IMPLIES (= (LIST k a) (LIST j b)) (AND (= k j) (= a b)))))))))
(dk-peel!)
(dk-conj-close!
  (lambda ()
    (if (equal? (cadr (dk-goal)) 'k)
        (ssl-component! '(LIST k a) '(LIST j b) 1)
        (ssl-component! '(LIST k a) '(LIST j b) 2))))
(qed 'node-pair-injective)

(sp (make-wff '(FORALL spa (FORALL x (FORALL y (IMPLIES (IN x (NODES spa)) (IMPLIES (IN y (NODES spa))
   (IMPLIES (= (NTH 1 x) (NTH 1 y)) (IMPLIES (= (NTH 2 x) (NTH 2 y)) (= x y))))))))))
(dk-peel!)
(ssl-node! 'spa 'x)
(ssl-node! 'spa 'y)
(dk-have! '(= (LIST (NTH 1 x) (NTH 2 x)) (LIST (NTH 1 y) (NTH 2 y)))
  (lambda () (subst '(= (NTH 1 x) (NTH 1 y))) (subst '(= (NTH 2 x) (NTH 2 y))) (rfl)))
(subst '(= x (LIST (NTH 1 x) (NTH 2 x))))
(subst '(= y (LIST (NTH 1 y) (NTH 2 y))))
(ass)
(qed 'node-ext)

;; (IN v SET) for v = SENT or RECEIVED (their values are numerals).
(define (ssl-const-set! cst def)
  (dk-have! `(IN ,cst SET)
    (lambda ()
      (let ((eqn (dk-cite! def)))
        (subst eqn)
        (dk-have! `(IN ,(caddr eqn) NN) (lambda () (arith)))
        (fact 'membership-implies-sethood (caddr eqn) 'NN)
        (ass)))))

(sp (make-wff '(FORALL T (FORALL K (FORALL d (IMPLIES (IN d (DIRECTED T K))
   (AND (OR (= (NTH 1 d) SENT) (= (NTH 1 d) RECEIVED))
        (AND (IN (NTH 2 d) (MSG-SET T K)) (= d (LIST (NTH 1 d) (NTH 2 d)))))))))))
(dk-peel!)
(let* ((cm (ssl-open-in! '(IN d (DIRECTED T K)) (dk-cite! 'directed-unfold 'T 'K)))
       (vs (ssl-unpack! (ssl-cart-open! cm)))
       (x (car vs)) (y (cadr vs)))
  (ssl-const-set! 'SENT 'sent-def)
  (ssl-const-set! 'RECEIVED 'received-def)
  (ssl-have-and! '(IN SENT SET) '(IN RECEIVED SET))
  (fact 'pairing-membership 'SENT 'RECEIVED)
  (inst*! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-head-is? (caddr f) 'IFF)
                                    (dk-contains? f 'RECEIVED)))
                   "the pairing universal")
          x)
  (let ((o `(OR (= ,x SENT) (= ,x RECEIVED))))
    (dk-have! o (lambda () (ssl-keep-prop! (iff-for `(IN ,x (PAIR SENT RECEIVED))) `(IN ,x (PAIR SENT RECEIVED)))))
    (dk-have! `(= (NTH 1 d) ,x) (lambda () (subst `(= d (LIST ,x ,y))) (nth-r) (rfl)))
    (dk-have! `(= (NTH 2 d) ,y) (lambda () (subst `(= d (LIST ,x ,y))) (nth-r) (rfl)))
    (subst `(= (NTH 1 d) ,x))
    (subst `(= (NTH 2 d) ,y))
    (dk-conj-close! (lambda () (ass)))))
(qed 'directed-parts)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
   (IN (NTH (NTH 1 n) ((STRAND-MAP spa) (NTH 2 n))) (DIRECTED (TOKENS spa) (KEYS spa)))))))))
(dk-peel!)
(ssl-node! 'spa 'n)
(fact 'strand-at-id 'spa '(NTH 2 n))
(ssl-have-and! '(IN (NTH 1 n) NN) '(IN ((STRAND-MAP spa) (NTH 2 n)) (TUPLES (DIRECTED (TOKENS spa) (KEYS spa))))
               '(<= 1 (NTH 1 n)) '(<= (NTH 1 n) (LENGTH ((STRAND-MAP spa) (NTH 2 n)))))
(fact 'nth-in-range '(DIRECTED (TOKENS spa) (KEYS spa)) '(NTH 1 n) '((STRAND-MAP spa) (NTH 2 n)))
(ass)
(qed 'node-step-in-directed)

;; The directed message at the node N of SPA (typed), its parts landed; returns it.
(define (ssl-step! spa n)
  (let ((d `(NTH (NTH 1 ,n) ((STRAND-MAP ,spa) (NTH 2 ,n)))))
    (fact 'node-step-in-directed spa n)
    (fact 'directed-parts `(TOKENS ,spa) `(KEYS ,spa) d)
    (dk-split-all!)
    d))

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
   (IN (NODE-CONTENT spa n) (MSG-SET (TOKENS spa) (KEYS spa)))))))))
(dk-peel!)
(ssl-step! 'spa 'n)
(mac 'NODE-CONTENT)
(ass)
(qed 'node-content-in-msgs)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
   (OR (= (NODE-DIR spa n) SENT) (= (NODE-DIR spa n) RECEIVED))))))))
(dk-peel!)
(ssl-step! 'spa 'n)
(mac 'NODE-DIR)
(ass)
(qed 'node-dir-cases)

(sp (make-wff '(NOT (= SENT RECEIVED))))
(subst (dk-cite! 'sent-def))
(subst (dk-cite! 'received-def))
(arith)
(qed 'sent-ne-received)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
   (OR (IS-SENT spa n) (IS-RECEIVED spa n))))))))
(dk-peel!)
(fact 'node-dir-cases 'spa 'n)
(mac 'is-sent)
(mac 'is-received)
(ass)
(qed 'node-sent-or-received)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-SENT spa n) (NOT (IS-RECEIVED spa n)))))))
(dk-peel!)
(mac-h 'is-sent '(IS-SENT spa n))
(di)
(mac-h 'is-received '(IS-RECEIVED spa n))
(fact 'sent-ne-received)
(dk-have! '(= SENT RECEIVED)
  (lambda () (subst '(= SENT (NODE-DIR spa n))) (ass)))
(ai '(NOT (= SENT RECEIVED)))
(qed 'node-not-sent-and-received)

;;; A node's content and direction, read off the directed message at its index: the form
;;; every computation on a concrete strand uses (a quasi-equation, so no definedness is
;;; asserted; `subst' takes it as an equation).
(sp (make-wff '(FORALL spa (FORALL n (FORALL k (FORALL d
   (IMPLIES (= (NTH 1 n) k) (IMPLIES (= (NTH k ((STRAND-MAP spa) (NTH 2 n))) d)
     (AND (== (NODE-CONTENT spa n) (NTH 2 d)) (== (NODE-DIR spa n) (NTH 1 d)))))))))))
(dk-peel!)
(dk-conj-close!
  (lambda ()
    (if (dk-contains? (dk-goal) 'NODE-CONTENT) (mac 'NODE-CONTENT) (mac 'NODE-DIR))
    (subst '(= (NTH 1 n) k))
    (subst '(= (NTH k ((STRAND-MAP spa) (NTH 2 n))) d))
    (qrfl)))
(qed 'node-content-eq)

;;; -----------------------------------------------------------------------
;;; 2. The relations on nodes.

;; Open (SAME-STRAND-BEFORE spa x y) [or UPTO] on a lane, landing its four conjuncts.
(define (ssl-ssb! pred spa x y)
  (let ((hyp `(,pred ,spa ,x ,y))
        (lc (if (eq? pred 'SAME-STRAND-BEFORE) '< '<=)))
    (for-each (lambda (cl) (ssl-project! (if (eq? pred 'SAME-STRAND-BEFORE) 'same-strand-before 'same-strand-upto)
                                         hyp cl))
              (list `(IN ,x (NODES ,spa)) `(IN ,y (NODES ,spa)) `(= (NTH 2 ,x) (NTH 2 ,y))
                    `(,lc (NTH 1 ,x) (NTH 1 ,y))))))

(sp (make-wff '(FORALL spa (FORALL n (NOT (SAME-STRAND-BEFORE spa n n))))))
(dk-peel!)
(di)
(ssl-ssb! 'SAME-STRAND-BEFORE 'spa 'n 'n)
(ssl-node! 'spa 'n)
(fact 'nn-in-rr '(NTH 1 n))
(ai (dk-cite! 'rr-lt-irrefl '(NTH 1 n)))
(qed 'ssb-irreflexive)

(sp (make-wff '(FORALL spa (FORALL x (FORALL y (FORALL z
   (IMPLIES (SAME-STRAND-BEFORE spa x y) (IMPLIES (SAME-STRAND-BEFORE spa y z) (SAME-STRAND-BEFORE spa x z)))))))))
(dk-peel!)
(ssl-ssb! 'SAME-STRAND-BEFORE 'spa 'x 'y)
(ssl-ssb! 'SAME-STRAND-BEFORE 'spa 'y 'z)
(ssl-node! 'spa 'x) (ssl-node! 'spa 'y) (ssl-node! 'spa 'z)
(mac 'same-strand-before)
(dk-conj-close!
  (lambda ()
    (cond ((dk-asm? (dk-goal)) (ass))
          ((dk-head-is? (dk-goal) '=) (subst '(= (NTH 2 x) (NTH 2 y))) (ass))
          (#t (dk-nn! '(< (NTH 1 x) (NTH 1 y)) '(< (NTH 1 y) (NTH 1 z)))))))
(qed 'ssb-transitive)

(sp (make-wff '(FORALL spa (FORALL x (FORALL y
   (IMPLIES (SAME-STRAND-BEFORE spa x y) (SAME-STRAND-UPTO spa x y)))))))
(dk-peel!)
(ssl-ssb! 'SAME-STRAND-BEFORE 'spa 'x 'y)
(ssl-node! 'spa 'x) (ssl-node! 'spa 'y)
(mac 'same-strand-upto)
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal)) (ass) (dk-nn! '(< (NTH 1 x) (NTH 1 y))))))
(qed 'ssu-of-ssb)

(sp (make-wff '(FORALL spa (FORALL x (IMPLIES (IN x (NODES spa)) (SAME-STRAND-UPTO spa x x))))))
(dk-peel!)
(ssl-node! 'spa 'x)
(mac 'same-strand-upto)
(dk-conj-close!
  (lambda ()
    (cond ((dk-asm? (dk-goal)) (ass))
          ((dk-head-is? (dk-goal) '=) (rfl))
          (#t (dk-nn!)))))
(qed 'ssu-refl)

;;; ==>= is ==> u identity: the converse of the two above.
(sp (make-wff '(FORALL spa (FORALL x (FORALL y (IMPLIES (SAME-STRAND-UPTO spa x y)
   (OR (SAME-STRAND-BEFORE spa x y) (= x y))))))))
(dk-peel!)
(ssl-ssb! 'SAME-STRAND-UPTO 'spa 'x 'y)
(ssl-node! 'spa 'x) (ssl-node! 'spa 'y)
(use-em '(= (NTH 1 x) (NTH 1 y))
  (lambda ()
    (oi-r)
    (fact 'node-ext 'spa 'x 'y)
    (ass))
  (lambda ()
    (oi-l)
    (mac 'same-strand-before)
    (dk-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal))
            (ass)
            (begin (mac '<) (dk-conj-close! (lambda () (ass)))))))))
(qed 'ssu-cases)

(sp (make-wff '(FORALL spa (FORALL x (FORALL y (IMPLIES (SENDS-TO spa x y)
   (AND (IS-SENT spa x) (AND (IS-RECEIVED spa y) (= (NODE-CONTENT spa x) (NODE-CONTENT spa y))))))))))
(dk-peel!)
(ssl-proj! 'sends-to '(SENDS-TO spa x y))
(qed 'sends-to-dirs)

;;; -----------------------------------------------------------------------
;;; 3. Bundles: the law projections.

(define (ssl-bundle-proj! claim)
  (di) (di)
  (ssl-proj! 'is-bundle '(IS-BUNDLE c)))

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IS-STRAND-SPACE (BSPACE c))))))
(ssl-bundle-proj! #f)
(qed 'bundle-space)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IN (BNODES c) SET)))))
(ssl-bundle-proj! #f)
(qed 'bundle-nodes-set)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IN (BSEND c) (POWER (CARTESIAN (BNODES c) (BNODES c))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-send-typing)


(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c)
   (FORALL ssx_ (IMPLIES (IN ssx_ (BNODES c)) (IN ssx_ (NODES (BSPACE c)))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-nodes-in-space)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IN (CARD (BNODES c)) NN)))))
(ssl-bundle-proj! #f)
(qed 'bundle-finite)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c)
   (FORALL ssx_ (FORALL ssy_ (IMPLIES (IN (LIST ssx_ ssy_) (BSEND c)) (SENDS-TO (BSPACE c) ssx_ ssy_))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-send-sends)
;;; (bundle-next-typing, bundle-next-next, -- the projections of the BNEXT slot and
;;; its two laws -- were here until 2026-10-07; the slot is dropped, see strand-spaces.scm.)


(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c)
   (FORALL ssy_ (IMPLIES (IN ssy_ (BNODES c)) (IMPLIES (IS-RECEIVED (BSPACE c) ssy_)
     (FORSOME ssx_ (AND (IN (LIST ssx_ ssy_) (BSEND c))
                        (FORALL ssz_ (IMPLIES (IN (LIST ssz_ ssy_) (BSEND c)) (= ssz_ ssx_))))))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-received-sender)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c)
   (FORALL ssy_ (IMPLIES (IN ssy_ (BNODES c))
     (FORALL ssx_ (IMPLIES (SAME-STRAND-BEFORE (BSPACE c) ssx_ ssy_) (IN ssx_ (BNODES c))))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-ssb-closed)


(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c)
   (FORALL ssx_ (NOT (IN (LIST ssx_ ssx_) (PREC-STRICT (BSPACE c) (BNODES c) (BSEND c)))))))))
(ssl-bundle-proj! #f)
(qed 'bundle-acyclic)

;;; A pair in a relation on ND has both ends in ND.
(sp (make-wff '(FORALL r (FORALL ND (FORALL x (FORALL y
   (IMPLIES (IN r (POWER (CARTESIAN ND ND))) (IMPLIES (IN (LIST x y) r) (AND (IN x ND) (IN y ND))))))))))
(dk-peel!)
(dk-have! '(IN (LIST x y) (CARTESIAN ND ND))
  (lambda ()
    (mac-h 'power-set-membership '(IN r (POWER (CARTESIAN ND ND))))
    (dk-split-all!)
    (dk-apply! (dk-pick (lambda (f) (dk-head-is? f 'FORALL)) "the power-set universal") '(LIST x y))
    (ass)))
(fact 'pair-in-cartesian-parts 'ND 'ND 'x 'y)
(ass)
(qed 'pair-in-power-box)

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IS-BUNDLE c) (IMPLIES (IN (LIST x y) (BSEND c))
   (AND (IN x (BNODES c)) (IN y (BNODES c))))))))))
(dk-peel!)
(fact 'bundle-send-typing 'c)
(fact 'pair-in-power-box '(BSEND c) '(BNODES c) 'x 'y)
(ass)
(qed 'bundle-send-nodes)

;;; -----------------------------------------------------------------------
;;; 4. Causal precedence on loose data (spa, ND, ED): PREC-STRICT.

(define (ssl-ps spa nd ed) `(PREC-STRICT ,spa ,nd ,ed))

;; (IN (LIST x y) PS) in context: land x, y in ND and the universal "every closed q in
;; POWER(ND x ND) holds [x, y]", which is returned.
(define (ssl-ps-open! spa nd ed x y)
  (let* ((mem `(IN (LIST ,x ,y) ,(ssl-ps spa nd ed)))
         (sepm (ssl-open-in! mem (dk-cite! 'prec-strict-unfold spa nd ed))))
    (let* ((landed (dk-landed (lambda () (sep-me sepm))))
           (univ (or (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed)
                     (error "ssl-ps-open!: no universal landed"))))
      (fact 'pair-in-cartesian-parts nd nd x y)
      (dk-split-all!)
      univ)))

;; The kind of a clause of IS-PREC-CLOSED, by its leading binders.
(define (ssl-pc-kind f)
  (let loop ((f f) (k 0))
    (if (dk-head-is? f 'FORALL) (loop (caddr f) (+ k 1))
        (case k ((2) 'send) ((1) 'ssb) (else 'trans)))))

;; The goal (IN (LIST x y) PS) with x, y in ND in context; PRE then STEP as in the messages file.
(define (ssl-ps-intro! spa nd ed x y pre step)
  (mac 'PREC-STRICT)
  (in-sep! (lambda () (fact 'pair-in-cartesian nd nd x y) (ass))
           (lambda ()
             (dk-peel!)
             (let* ((q (caddr (dk-goal)))
                    (closed `(IS-PREC-CLOSED ,spa ,nd ,ed ,q)))
               (pre q)
               (mac-h 'is-prec-closed closed)
               (dk-split-all!)
               (let ((clause-of (lambda (kind)
                                  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL)
                                                                   (dk-contains? f q)
                                                                   (eq? (ssl-pc-kind f) kind)))
                                                  (dk-asms))
                                      (error "ssl-ps-intro!: no clause" kind)))))
                 (step q clause-of))))))

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (FORALL x (FORALL y
   (IMPLIES (IN (LIST x y) (PREC-STRICT spa ND ED)) (AND (IN x ND) (IN y ND))))))))))
(dk-peel!)
(ssl-ps-open! 'spa 'ND 'ED 'x 'y)
(dk-conj-close! (lambda () (ass)))
(qed 'ps-in-box)

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (FORALL r
   (IMPLIES (IN r (POWER (CARTESIAN ND ND))) (IMPLIES (IS-PREC-CLOSED spa ND ED r)
     (FORALL x (FORALL y (IMPLIES (IN (LIST x y) (PREC-STRICT spa ND ED)) (IN (LIST x y) r))))))))))))
(dk-peel!)
(dk-apply! (ssl-ps-open! 'spa 'ND 'ED 'x 'y) 'r)
(ass)
(qed 'ps-least)

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (FORALL x (FORALL y
   (IMPLIES (IN ED (POWER (CARTESIAN ND ND))) (IMPLIES (IN (LIST x y) ED)
     (IN (LIST x y) (PREC-STRICT spa ND ED)))))))))))
(dk-peel!)
(fact 'pair-in-power-box 'ED 'ND 'x 'y)
(dk-split-all!)
(ssl-ps-intro! 'spa 'ND 'ED 'x 'y (lambda (q) #t)
  (lambda (q clause-of) (dk-apply! (clause-of 'send) 'x 'y) (ass)))
(qed 'ps-send)

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (FORALL x (FORALL y
   (IMPLIES (IN x ND) (IMPLIES (IN y ND) (IMPLIES (SAME-STRAND-BEFORE spa x y)
     (IN (LIST x y) (PREC-STRICT spa ND ED))))))))))))
(dk-peel!)
(ssl-ps-intro! 'spa 'ND 'ED 'x 'y (lambda (q) #t)
  (lambda (q clause-of) (dk-apply! (clause-of 'ssb) 'x 'y) (ass)))
(qed 'ps-ssb)

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (FORALL x (FORALL y (FORALL z
   (IMPLIES (IN (LIST x y) (PREC-STRICT spa ND ED)) (IMPLIES (IN (LIST y z) (PREC-STRICT spa ND ED))
     (IN (LIST x z) (PREC-STRICT spa ND ED))))))))))))
(dk-peel!)
(let* ((u1 (ssl-ps-open! 'spa 'ND 'ED 'x 'y))
       (u2 (ssl-ps-open! 'spa 'ND 'ED 'y 'z)))
  (ssl-ps-intro! 'spa 'ND 'ED 'x 'z
    (lambda (q) (dk-apply! u1 q) (dk-apply! u2 q))
    (lambda (q clause-of) (dk-apply! (clause-of 'trans) 'x 'y 'z) (ass))))
(qed 'ps-trans)

;;; On a bundle.

;; (IN p (PRECEDES-STRICT c)) <-> (IN p (PREC-STRICT ...)): land the other spelling.
(define (ssl-ps-of-bundle! c p)
  (let* ((eqn (dk-cite! 'precedes-strict-unfold c))
         (claim `(IN ,p ,(caddr eqn))))
    (dk-have! claim (lambda () (subst `(= ,(caddr eqn) (PRECEDES-STRICT ,c))) (ass)))
    claim))
(define (ssl-bundle-of-ps! c p)
  (let ((claim `(IN ,p (PRECEDES-STRICT ,c))))
    (dk-have! claim (lambda () (mac 'PRECEDES-STRICT) (ass)))
    claim))

(sp (make-wff '(FORALL c (FORALL x (FORALL y (FORALL z (IMPLIES (IS-BUNDLE c)
   (IMPLIES (IN (LIST x y) (PRECEDES-STRICT c)) (IMPLIES (IN (LIST y z) (PRECEDES-STRICT c))
     (IN (LIST x z) (PRECEDES-STRICT c)))))))))))
(dk-peel!)
(ssl-ps-of-bundle! 'c '(LIST x y))
(ssl-ps-of-bundle! 'c '(LIST y z))
(mac 'PRECEDES-STRICT)
(fact 'ps-trans '(BSPACE c) '(BNODES c) '(BSEND c) 'x 'y 'z)
(ass)
(qed 'precedes-strict-trans)

(sp (make-wff '(FORALL c (FORALL x (IMPLIES (IS-BUNDLE c) (NOT (IN (LIST x x) (PRECEDES-STRICT c))))))))
(dk-peel!)
(di)
(ssl-ps-of-bundle! 'c '(LIST x x))
(fact 'bundle-acyclic 'c 'x)
(ai `(NOT (IN (LIST x x) (PREC-STRICT (BSPACE c) (BNODES c) (BSEND c)))))
(qed 'precedes-strict-irreflexive)

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IS-BUNDLE c) (IMPLIES (IN (LIST x y) (BSEND c))
   (IN (LIST x y) (PRECEDES-STRICT c)))))))))
(dk-peel!)
(fact 'bundle-send-typing 'c)
(mac 'PRECEDES-STRICT)
(fact 'ps-send '(BSPACE c) '(BNODES c) '(BSEND c) 'x 'y)
(ass)
(qed 'bundle-send-precedes)

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IS-BUNDLE c) (IMPLIES (IN y (BNODES c))
   (IMPLIES (SAME-STRAND-BEFORE (BSPACE c) x y) (IN (LIST x y) (PRECEDES-STRICT c))))))))))
(dk-peel!)
(dk-apply! (dk-cite! 'bundle-ssb-closed 'c 'y) 'x)
(mac 'PRECEDES-STRICT)
(fact 'ps-ssb '(BSPACE c) '(BNODES c) '(BSEND c) 'x 'y)
(ass)
(qed 'bundle-ssb-precedes)

;;; PRECEDES = PRECEDES-STRICT u the identity on BNODES.
(define (ssl-id-rel c) `(SEP ssp_ (CARTESIAN (BNODES ,c) (BNODES ,c)) (= (NTH 1 ssp_) (NTH 2 ssp_))))

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IS-BUNDLE c) (IMPLIES (IN (LIST x y) (PRECEDES-STRICT c))
   (IN (LIST x y) (PRECEDES c)))))))))
(dk-peel!)
(mac 'PRECEDES)
(fact 'union-membership '(PRECEDES-STRICT c) (ssl-id-rel 'c) '(LIST x y))
(ssl-keep-prop! (iff-for `(IN (LIST x y) (UNION (PRECEDES-STRICT c) ,(ssl-id-rel 'c))))
                '(IN (LIST x y) (PRECEDES-STRICT c)))
(qed 'precedes-intro-strict)

(sp (make-wff '(FORALL c (FORALL x (IMPLIES (IN x (BNODES c)) (IN (LIST x x) (PRECEDES c)))))))
(dk-peel!)
(mac 'PRECEDES)
(dk-have! `(IN (LIST x x) ,(ssl-id-rel 'c))
  (lambda ()
    (in-sep! (lambda () (fact 'pair-in-cartesian '(BNODES c) '(BNODES c) 'x 'x) (ass))
             (lambda () (nth-r) (rfl)))))
(fact 'union-membership '(PRECEDES-STRICT c) (ssl-id-rel 'c) '(LIST x x))
(ssl-keep-prop! (iff-for `(IN (LIST x x) (UNION (PRECEDES-STRICT c) ,(ssl-id-rel 'c))))
                `(IN (LIST x x) ,(ssl-id-rel 'c)))
(qed 'precedes-refl)

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IN (LIST x y) (PRECEDES c))
   (OR (IN (LIST x y) (PRECEDES-STRICT c)) (AND (= x y) (IN x (BNODES c))))))))))
(dk-peel!)
(let* ((um (ssl-open-in! '(IN (LIST x y) (PRECEDES c)) (dk-cite! 'precedes-unfold 'c)))
       (o `(OR (IN (LIST x y) (PRECEDES-STRICT c)) (IN (LIST x y) ,(ssl-id-rel 'c)))))
  (dk-have! o (lambda () (fact 'union-membership '(PRECEDES-STRICT c) (ssl-id-rel 'c) '(LIST x y))
                         (ssl-keep-prop! (iff-for um) um)))
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (if (dk-asm? '(IN (LIST x y) (PRECEDES-STRICT c)))
          (begin (oi-l) (ass))
          (begin
            (oi-r)
            (sep-me `(IN (LIST x y) ,(ssl-id-rel 'c)))
            (fact 'pair-in-cartesian-parts '(BNODES c) '(BNODES c) 'x 'y)
            (dk-split-all!)
            (let ((imp '(IMPLIES (= (NTH 1 (LIST x y)) (NTH 2 (LIST x y))) (= x y))))
              (dk-have! imp (lambda () (nth-r) (di) (ass)))
              (detach! imp))
            (dk-conj-close! (lambda () (ass))))))))
(qed 'precedes-elim)

;;; INVERSION: a strictly preceding pair is reached by a LAST edge -- a send edge or a
;;; same-strand step into y -- from x itself or from a node x strictly precedes.  The one
;;; device: ps-least at the separation of PREC-STRICT by that condition.
(define (ssl-last-cond spa nd ed u v)
  `(FORSOME slz_ (AND (OR (IN (LIST slz_ ,v) ,ed) (AND (IN slz_ ,nd) (SAME-STRAND-BEFORE ,spa slz_ ,v)))
                      (OR (= slz_ ,u) (IN (LIST ,u slz_) (PREC-STRICT ,spa ,nd ,ed))))))
(define (ssl-pair-cond p cond2)
  `(FORSOME slu_ (FORSOME slv_ (AND (= ,p (LIST slu_ slv_)) ,(cond2 'slu_ 'slv_)))))

;; (IN (LIST a b) RR) in context, RR the SEP by (pair-cond COND2): land COND2(a, b).
(define (ssl-pair-cond-open! rr a b cond2)
  (sep-me `(IN (LIST ,a ,b) ,rr))
  (let* ((ex (or (find-first (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f `(LIST ,a ,b))))
                             (dk-asms))
                 (error "ssl-pair-cond-open!: no pair condition landed")))
         (vs (ssl-unpack! ex 2))
         (u (car vs)) (v (cadr vs))
         (claim (cond2 a b)))
    (dk-have! `(= ,a ,u) (lambda () (ssl-component! `(LIST ,a ,b) `(LIST ,u ,v) 1)))
    (dk-have! `(= ,b ,v) (lambda () (ssl-component! `(LIST ,a ,b) `(LIST ,u ,v) 2)))
    (dk-have! claim (lambda () (subst `(= ,a ,u)) (subst `(= ,b ,v)) (ass)))
    claim))

;; The goal (IN (LIST a b) RR): the PS membership in context, the condition by COND-THUNK.
(define (ssl-pair-cond-intro! a b cond-thunk)
  (in-sep! (lambda () (ass))
           (lambda ()
             (ew a) (ew b)
             (dk-each-leaf! (lambda () (di))
               (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (cond-thunk)))))))

(sp (make-wff '(FORALL spa (FORALL ND (FORALL ED (IMPLIES (IN ND SET) (IMPLIES (IN ED (POWER (CARTESIAN ND ND)))
  (FORALL x (FORALL y (IMPLIES (IN (LIST x y) (PREC-STRICT spa ND ED))
    (FORSOME z (AND (OR (IN (LIST z y) ED) (AND (IN z ND) (SAME-STRAND-BEFORE spa z y)))
                    (OR (= z x) (IN (LIST x z) (PREC-STRICT spa ND ED)))))))))))))))
(dk-peel!)
(let* ((ps '(PREC-STRICT spa ND ED))
       (cond2 (lambda (u v) (ssl-last-cond 'spa 'ND 'ED u v)))
       (rr `(SEP slp_ ,ps ,(ssl-pair-cond 'slp_ cond2))))
  ;; RR is a subset of ND x ND, a set
  (dk-have! `(IN ,rr (POWER (CARTESIAN ND ND)))
    (lambda ()
      (ssl-have-and! '(IN ND SET) '(IN ND SET))
      (fact 'cartesian-set-iff 'ND 'ND)
      (dk-have! '(IN (CARTESIAN ND ND) SET)
        (lambda () (ssl-keep-prop! (iff-for '(IN (CARTESIAN ND ND) SET)) '(AND (IN ND SET) (IN ND SET)))))
      (mac 'power-set-membership)
      (dk-each-leaf! (lambda () (di))
        (lambda ()
          (if (dk-head-is? (dk-goal) 'IN)
              (dk-each-leaf! (lambda () (sep-set))
                (lambda ()
                  (if (dk-asm? (dk-goal)) (ass)
                      (let ((eqn (dk-cite! 'prec-strict-unfold 'spa 'ND 'ED)))
                        (subst eqn)
                        (dk-each-leaf! (lambda () (sep-set)) (lambda () (ass)))))))
              (let* ((landed (dk-peel!))
                     (w (cadr (dk-goal))))
                (sep-me `(IN ,w ,rr))
                (let ((sm (ssl-open-in! `(IN ,w ,ps) (dk-cite! 'prec-strict-unfold 'spa 'ND 'ED))))
                  (sep-me sm)
                  (ass))))))))
  ;; RR is closed
  (dk-have! `(IS-PREC-CLOSED spa ND ED ,rr)
    (lambda ()
      (mac 'is-prec-closed)
      (dk-conj-close!
        (lambda ()
          (let ((kind (ssl-pc-kind (dk-goal))))
            (dk-peel!)
            (let* ((pr (cadr (dk-goal))) (x (cadr pr)) (y (caddr pr)))
              (case kind
                ((send)
                 (fact 'ps-send 'spa 'ND 'ED x y)
                 (ssl-pair-cond-intro! x y
                   (lambda () (ew x) (dk-conj-close!
                                       (lambda () (if (dk-head-is? (cadr (dk-goal)) '=)
                                                      (begin (oi-l) (rfl))
                                                      (begin (oi-l) (ass))))))))
                ((ssb)
                 (fact 'ps-ssb 'spa 'ND 'ED x y)
                 (ssl-pair-cond-intro! x y
                   (lambda () (ew x)
                     (dk-conj-close!
                       (lambda ()
                         (cond ((not (dk-head-is? (dk-goal) 'OR)) (ass))
                               ((dk-head-is? (caddr (dk-goal)) 'AND)
                                (oi-r) (dk-conj-close! (lambda () (ass))))
                               (#t (oi-l) (rfl))))))))
                (else
                 ;; [x, y] and [y, w] in RR: the last edge of [y, w] serves [x, w]
                 (let* ((mid (caddr (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (alpha-equiv? (caddr f) rr)
                                                                       (equal? (cadr (cadr f)) x)))
                                                     (dk-asms)))))
                        (dummy0 (ssl-pair-cond-open! rr x mid cond2))
                        (h2 (ssl-pair-cond-open! rr mid y cond2))
                        (zz (dk-skolem! h2 'top)))
                   (fact 'ps-trans 'spa 'ND 'ED x mid y)
                   (ssl-pair-cond-intro! x y
                     (lambda ()
                       (ew zz)
                       (dk-conj-close!
                         (lambda ()
                           (if (not (dk-head-is? (cadr (dk-goal)) '=))
                               (ass)
                               ;; z = x or [x, z] in PS: from z = mid or [mid, z] in PS
                               (let ((o (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f `(= ,zz ,mid))))
                                                 "z = mid or [mid, z] in PS")))
                                 (oi-r)
                                 (dk-each-leaf! (lambda () (ai o))
                                   (lambda ()
                                     (if (dk-asm? `(= ,zz ,mid))
                                         (begin (subst `(= ,zz ,mid)) (ass))
                                         (begin (fact 'ps-trans 'spa 'ND 'ED x mid zz) (ass))))))))))))))))))))
  (fact 'ps-least 'spa 'ND 'ED rr)
  (dk-apply! (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f rr)
                                              (not (dk-contains? f 'IS-PREC-CLOSED))))
                             (dk-asms))
                 (error "ps-last-step: ps-least did not detach"))
             'x 'y)
  (ssl-pair-cond-open! rr 'x 'y cond2)
  (dk-ass!))
(qed 'ps-last-step)

;;; -----------------------------------------------------------------------
;;; 5. LEMMA 2.7: PRECEDES is a partial order on BNODES; minimal elements.

(define (ssl-precedes-cases! c x y on-strict on-eq)
  (let ((o (dk-cite! 'precedes-elim c x y)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? `(IN (LIST ,x ,y) (PRECEDES-STRICT ,c)))
            (on-strict)
            (begin (dk-split-all!) (on-eq)))))))

(sp (make-wff '(FORALL c (FORALL x (FORALL y (FORALL z (IMPLIES (IS-BUNDLE c)
   (IMPLIES (IN (LIST x y) (PRECEDES c)) (IMPLIES (IN (LIST y z) (PRECEDES c)) (IN (LIST x z) (PRECEDES c)))))))))))
(dk-peel!)
(ssl-precedes-cases! 'c 'x 'y
  (lambda ()
    (ssl-precedes-cases! 'c 'y 'z
      (lambda ()
        (fact 'precedes-strict-trans 'c 'x 'y 'z)
        (fact 'precedes-intro-strict 'c 'x 'z)
        (ass))
      (lambda ()
        (subst '(= z y))
        (fact 'precedes-intro-strict 'c 'x 'y)
        (ass))))
  (lambda ()
    (subst '(= x y))
    (ass)))
(qed 'precedes-trans)

(sp (make-wff '(FORALL c (FORALL x (FORALL y (IMPLIES (IS-BUNDLE c)
   (IMPLIES (IN (LIST x y) (PRECEDES c)) (IMPLIES (IN (LIST y x) (PRECEDES c)) (= x y)))))))))
(dk-peel!)
(ssl-precedes-cases! 'c 'x 'y
  (lambda ()
    (ssl-precedes-cases! 'c 'y 'x
      (lambda ()
        (fact 'precedes-strict-trans 'c 'x 'y 'x)
        (ai (dk-cite! 'precedes-strict-irreflexive 'c 'x)))
      (lambda () (subst '(= x y)) (rfl))))
  (lambda () (ass)))
(qed 'precedes-antisym)

;; (IN X SET) for X a SEP over a set in context, or a CARTESIAN of sets.
(define (ssl-cart-set! a)
  (let ((goal `(IN (CARTESIAN ,a ,a) SET)))
    (ssl-have-and! `(IN ,a SET) `(IN ,a SET))
    (fact 'cartesian-set-iff a a)
    (dk-have! goal (lambda () (ssl-keep-prop! (iff-for goal) `(AND (IN ,a SET) (IN ,a SET)))))
    goal))

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IN (PRECEDES c) SET)))))
(dk-peel!)
(fact 'bundle-nodes-set 'c)
(ssl-cart-set! '(BNODES c))
(dk-have! '(IN (PRECEDES-STRICT c) SET)
  (lambda () (mac 'PRECEDES-STRICT) (mac 'PREC-STRICT) (dk-each-leaf! (lambda () (sep-set)) (lambda () (ass)))))
(dk-have! `(IN ,(ssl-id-rel 'c) SET) (lambda () (dk-each-leaf! (lambda () (sep-set)) (lambda () (ass)))))
(ssl-have-and! '(IN (PRECEDES-STRICT c) SET) `(IN ,(ssl-id-rel 'c) SET))
(fact 'union-set-closure '(PRECEDES-STRICT c) (ssl-id-rel 'c))
(mac 'PRECEDES)
(ass)
(qed 'precedes-set)

(sp (make-wff '(FORALL c (IMPLIES (IS-BUNDLE c) (IS-PARTIAL-ORDER (BNODES c) (PRECEDES c))))))
(dk-peel!)
(mac 'is-partial-order)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((dk-asm? g) (ass))
            ((equal? g '(IN (BNODES c) SET)) (fact 'bundle-nodes-set 'c) (ass))
            ((equal? g '(IN (PRECEDES c) SET)) (fact 'precedes-set 'c) (ass))
            (#t
             (let* ((landed (dk-peel!)) (g2 (dk-goal)))
               (cond
                 ((dk-head-is? g2 '=)                                   ; antisymmetry
                  (dk-split-all!)
                  (fact 'precedes-antisym 'c (cadr g2) (caddr g2))
                  (ass))
                 ((let ((pr (cadr g2))) (equal? (cadr pr) (caddr pr)))   ; reflexivity
                  (fact 'precedes-refl 'c (cadr (cadr g2)))
                  (ass))
                 (#t                                                     ; transitivity
                  (dk-split-all!)
                  (let* ((x (cadr (cadr g2))) (z (caddr (cadr g2)))
                         (mid (caddr (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN)
                                                                        (dk-head-is? (cadr f) 'LIST)
                                                                        (equal? (cadr (cadr f)) x)
                                                                        (equal? (caddr f) '(PRECEDES c))))
                                                       (dk-asms))))))
                    (fact 'precedes-trans 'c x mid z)
                    (ass))))))))))
(qed 'precedes-partial-order)

;;; MINIMAL ELEMENTS, for any transitive irreflexive relation R on a finite set: by
;;; finite-set-induction at the class of the sets that are empty or have an R-minimal member.
;;; The step ADDS a point x to S: if S is empty x is minimal; else S has a minimal m, and
;;; either [x, m] in R -- then x is minimal in S u {x} (a z in S with [z, x] in R would give
;;; [z, m] in R) -- or m stays minimal.

;; The class, with R the relation (a symbol in context).
(define (ssl-min-prop r xs)
  `(IMPLIES (FORSOME mnw_ (IN mnw_ ,xs))
            (FORSOME mnm_ (AND (IN mnm_ ,xs) (FORALL mnz_ (IMPLIES (IN mnz_ ,xs) (NOT (IN (LIST mnz_ mnm_) ,r))))))))
(define (ssl-min-class r) `(COMP mnx_ ,(ssl-min-prop r 'mnx_)))

;; With (IN z (UNION S (PAIR x x))) and (IN x SET) in context: ON-S with (IN z S), ON-EQ
;; with (= z x).
(define (ssl-union-cases! z ss x on-s on-eq)
  (let* ((mem `(IN ,z (UNION ,ss (PAIR ,x ,x))))
         (o `(OR (IN ,z ,ss) (IN ,z (PAIR ,x ,x)))))
    (dk-have! o (lambda () (fact 'union-membership ss `(PAIR ,x ,x) z) (ssl-keep-prop! (iff-for mem) mem)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? `(IN ,z ,ss))
            (on-s)
            (begin (fact 'pair-self-eq x z) (on-eq)))))))

;; The goal (IN v (UNION S (PAIR x x))) from (IN v S), or v = x with (IN x SET).
(define (ssl-union-in! v ss x)
  (let ((g `(IN ,v (UNION ,ss (PAIR ,x ,x)))))
    (fact 'union-membership ss `(PAIR ,x ,x) v)
    (if (dk-asm? `(IN ,v ,ss))
        (ssl-keep-prop! (iff-for g) `(IN ,v ,ss))
        (begin (fact 'pair-self-member x)
               (ssl-keep-prop! (iff-for g) `(IN ,x (PAIR ,x ,x)))))))

;; With (= z x) and the formula F(z) in context, land F(x) (no hypothesis-side subst: the
;; implication F(z) => F(x) is proved by rewriting z to x in its goal).
(define (ssl-transport! fz z x)
  (let* ((fx (subst-free z x fz))
         (imp `(IMPLIES ,fz ,fx)))
    (dk-have! imp (lambda () (subst `(= ,z ,x)) (di) (ass)))
    (detach! imp)
    fx))

(sp (make-wff '(FORALL R (IMPLIES (FORALL x (FORALL y (FORALL z (IMPLIES (IN (LIST x y) R)
                                   (IMPLIES (IN (LIST y z) R) (IN (LIST x z) R))))))
   (IMPLIES (FORALL x (NOT (IN (LIST x x) R)))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN) (IMPLIES (FORSOME w (IN w S))
       (FORSOME m (AND (IN m S) (FORALL z (IMPLIES (IN z S) (NOT (IN (LIST z m) R)))))))))))))))
(let* ((landed (dk-peel!))
       (g0 (dk-goal))
       (ss (caddr (cadr (caddr g0))))                   ; read S off (FORSOME m (AND (IN m S) ...))
       (h-trans (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'IMPLIES))) landed))
       (h-irr (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (not (dk-contains? f 'IMPLIES)))) landed))
       (r (caddr (cadr (caddr h-irr))))                  ; (FORALL x (NOT (IN (LIST x x) R)))
       (cc (ssl-min-class r))
       (ind0 (lookup-theorem 'finite-set-induction))
       (ind (subst-free (quantifier-var ind0) cc (quantifier-body ind0)))
       (prem (cadr ind))
       (h-base (cadr prem))
       (h-step (caddr prem)))
  ;; base: the empty set has no member
  (dk-have! h-base
    (lambda ()
      (dk-each-leaf! (lambda () (comp-mi))
        (lambda ()
          (if (dk-head-is? (dk-goal) 'IN)
              (begin (fact 'empty-set-is-set) (ass))
              (begin
                (di)
                (let* ((ex (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the member"))
                       (w (dk-skolem! ex)))
                  (fact 'empty-set-has-no-members w)
                  (ai `(NOT (IN ,w EMPTY-SET))))))))))
  ;; step: S finite with the property, x a new point
  (dk-have! h-step
    (lambda ()
      (dk-peel!)
      (dk-split-all!)
      (let* ((g (dk-goal))                                   ; (IN (UNION S (PAIR x x)) C)
             (un (cadr g)) (s1 (cadr un)) (x (cadr (caddr un))))
        (comp-me `(IN ,s1 ,cc))
        (dk-each-leaf! (lambda () (comp-mi))
          (lambda ()
            (if (dk-head-is? (dk-goal) 'IN)
                ;; S u {x} is a set
                (begin
                  (ssl-have-and! `(IN ,x SET) `(IN ,x SET))
                  (fact 'pairing x x)
                  (ssl-have-and! `(IN ,s1 SET) `(IN (PAIR ,x ,x) SET))
                  (fact 'union-set-closure s1 `(PAIR ,x ,x))
                  (ass))
                ;; the property at S u {x}
                (begin
                  (di)
                  (let ((nonempty `(FORSOME mnw_ (IN mnw_ ,s1)))
                        (min-of (lambda (m)                 ; claim: m is minimal in S u {x}
                                  `(FORALL mnz_ (IMPLIES (IN mnz_ ,un) (NOT (IN (LIST mnz_ ,m) ,r)))))))
                    (use-em nonempty
                      ;; S nonempty: its minimal m0
                      (lambda ()
                        (let* ((pS (dk-pick (lambda (f) (and (dk-head-is? f 'IMPLIES) (alpha-equiv? (cadr f) nonempty)))
                                            "the property at S"))
                               (ex (dk-landed-1 (lambda () (detach! pS))))
                               (m0 (dk-skolem! ex))
                               (minS (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f m0)))
                                              "m0 minimal in S")))
                          (use-em `(IN (LIST ,x ,m0) ,r)
                            ;; [x, m0] in R: x is minimal
                            (lambda ()
                              (ew x)
                              (dk-conj-close!
                                (lambda ()
                                  (if (dk-head-is? (dk-goal) 'IN)
                                      (ssl-union-in! x s1 x)
                                      (begin
                                        (dk-peel!)
                                        (di)                         ; [z, x] in R; goal FALSITY
                                        (let ((z (cadr (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (cadr f) 'LIST)
                                                                                         (equal? (caddr (cadr f)) x) (equal? (caddr f) r)))
                                                                          (dk-asms))))))
                                          (ssl-union-cases! z s1 x
                                            (lambda ()
                                              (dk-apply! h-trans z x m0)
                                              (ai (dk-apply! minS z)))
                                            (lambda ()
                                              (ssl-transport! `(IN (LIST ,z ,x) ,r) z x)
                                              (ai (dk-apply! h-irr x))))))))))
                            ;; [x, m0] not in R: m0 stays minimal
                            (lambda ()
                              (ew m0)
                              (dk-conj-close!
                                (lambda ()
                                  (if (dk-head-is? (dk-goal) 'IN)
                                      (ssl-union-in! m0 s1 x)
                                      (begin
                                        (dk-peel!)
                                        (let ((z (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) un)))
                                                                   (dk-asms)))))
                                          (ssl-union-cases! z s1 x
                                            (lambda () (dk-apply! minS z) (ass))
                                            (lambda ()
                                              (dk-have! `(IMPLIES (NOT (IN (LIST ,x ,m0) ,r)) (NOT (IN (LIST ,z ,m0) ,r)))
                                                (lambda () (subst `(= ,z ,x)) (di) (ass)))
                                              (detach! `(IMPLIES (NOT (IN (LIST ,x ,m0) ,r)) (NOT (IN (LIST ,z ,m0) ,r))))
                                              (ass))))))))))))
                      ;; S empty: x is minimal
                      (lambda ()
                        (ew x)
                        (dk-conj-close!
                          (lambda ()
                            (if (dk-head-is? (dk-goal) 'IN)
                                (ssl-union-in! x s1 x)
                                (begin
                                  (dk-peel!)
                                  (let ((z (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) un)))
                                                             (dk-asms)))))
                                    (ssl-union-cases! z s1 x
                                      (lambda ()
                                        (dk-have! nonempty (lambda () (ew z) (ass)))
                                        (ai `(NOT ,nonempty)))
                                      (lambda ()
                                        (dk-have! `(IMPLIES (NOT (IN (LIST ,x ,x) ,r)) (NOT (IN (LIST ,z ,x) ,r)))
                                          (lambda () (subst `(= ,z ,x)) (di) (ass)))
                                        (dk-apply! h-irr x)
                                        (detach! `(IMPLIES (NOT (IN (LIST ,x ,x) ,r)) (NOT (IN (LIST ,z ,x) ,r))))
                                        (ass))))))))))))))))))
  (dk-have! prem (lambda () (dk-conj-close! (lambda () (ass)))))
  (ssl-have-and! `(IN ,ss SET) `(IN (CARD ,ss) NN))
  (let* ((all (dk-cite! 'finite-set-induction cc))
         (inS (dk-apply! all ss)))
    (comp-me inS)
    (dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'IMPLIES) (dk-head-is? (cadr f) 'FORSOME)
                                         (dk-contains? (cadr f) ss)))
                        "the property at S")
               )
    (dk-ass!)))
(qed 'finite-strict-minimal)

;;; LEMMA 2.7 (iii): every nonempty set of nodes of a bundle has a PRECEDES-STRICT-minimal
;;; member.  The finiteness used is CARD(BNODES) in NN, inherited by S (card-subset-nn).
(sp (make-wff '(FORALL c (FORALL S (IMPLIES (IS-BUNDLE c)
   (IMPLIES (FORALL z (IMPLIES (IN z S) (IN z (BNODES c))))
   (IMPLIES (FORSOME w (IN w S))
     (FORSOME m (AND (IN m S) (FORALL z (IMPLIES (IN z S) (NOT (IN (LIST z m) (PRECEDES-STRICT c))))))))))))))
(dk-peel!)
(fact 'bundle-nodes-set 'c)
(fact 'bundle-finite 'c)
(dk-have! '(SUBSET S (BNODES c)) (lambda () (mac 'subset-def) (ass)))
(fact 'subclass-of-set-is-set 'S '(BNODES c))
(ssl-have-and! '(IN (BNODES c) SET) '(IN (CARD (BNODES c)) NN))
(ssl-have-and! '(IN S SET) '(FORALL z (IMPLIES (IN z S) (IN z (BNODES c)))))
(fact 'card-subset-nn '(BNODES c) 'S)
(let ((tr '(FORALL x (FORALL y (FORALL z (IMPLIES (IN (LIST x y) (PRECEDES-STRICT c))
              (IMPLIES (IN (LIST y z) (PRECEDES-STRICT c)) (IN (LIST x z) (PRECEDES-STRICT c))))))))
      (ir '(FORALL x (NOT (IN (LIST x x) (PRECEDES-STRICT c))))))
  (dk-have! tr (lambda () (dk-peel!) (let ((g (dk-goal)) (hs (dk-asms)))
                                       (let* ((x (cadr (cadr g))) (z (caddr (cadr g)))
                                              (y (caddr (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (cadr f) 'LIST)
                                                                                           (equal? (cadr (cadr f)) x)
                                                                                           (equal? (caddr f) '(PRECEDES-STRICT c))))
                                                                          hs)))))
                                         (fact 'precedes-strict-trans 'c x y z) (ass)))))
  (dk-have! ir (lambda () (let ((x (dk-di-var! (lambda (g) (cadr (cadr (cadr g))))))) (fact 'precedes-strict-irreflexive 'c x) (ass))))
  (fact 'finite-strict-minimal '(PRECEDES-STRICT c) 'S)
  (dk-ass!))
(qed 'bundle-minimal)

;;; The same with the paper's <= (Lemma 2.7's wording): no OTHER member of S precedes m.
(sp (make-wff '(FORALL c (FORALL S (IMPLIES (IS-BUNDLE c)
   (IMPLIES (FORALL z (IMPLIES (IN z S) (IN z (BNODES c))))
   (IMPLIES (FORSOME w (IN w S))
     (FORSOME m (AND (IN m S) (FORALL z (IMPLIES (IN z S) (IMPLIES (NOT (= z m)) (NOT (IN (LIST z m) (PRECEDES c)))))))))))))))
(dk-peel!)
(let* ((ex (dk-cite! 'bundle-minimal 'c 'S))
       (m (dk-skolem! ex))
       (minS (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f m) (dk-contains? f 'PRECEDES-STRICT)))
                      "m minimal")))
  (ew m)
  (dk-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal)) (ass)
          (begin
            (dk-peel!)
            (di)                                     ; [z, m] in PRECEDES; goal FALSITY
            (let ((z (cadr (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(PRECEDES c)))) (dk-asms))))))
              (ssl-precedes-cases! 'c z m
                (lambda () (ai (dk-apply! minS z)))
                (lambda () (ai `(NOT (= ,z ,m)))))))))))
(qed 'bundle-minimal-precedes)

;;; -----------------------------------------------------------------------
;;; 6. LEMMA 2.8, origination, LEMMA 2.9.

;;; LEMMA 2.8: a minimal member of a set of bundle nodes closed under "equal content" is SENT.
;;; Only the EXISTENCE half of the bundle's "unique sender" law is used (finding (d)).
(sp (make-wff '(FORALL c (FORALL S (FORALL n (IMPLIES (IS-BUNDLE c)
  (IMPLIES (FORALL z (IMPLIES (IN z S) (IN z (BNODES c))))
  (IMPLIES (FORALL x (FORALL y (IMPLIES (IN x (BNODES c)) (IMPLIES (IN y (BNODES c))
             (IMPLIES (= (NODE-CONTENT (BSPACE c) x) (NODE-CONTENT (BSPACE c) y)) (IMPLIES (IN y S) (IN x S)))))))
  (IMPLIES (IN n S)
  (IMPLIES (FORALL z (IMPLIES (IN z S) (NOT (IN (LIST z n) (PRECEDES-STRICT c)))))
    (IS-SENT (BSPACE c) n)))))))))))
(let* ((landed (dk-peel!))
       (sub (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (not (dk-contains? f 'NODE-CONTENT))
                                         (not (dk-contains? f 'PRECEDES-STRICT))))
                        landed))
       (clo (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'NODE-CONTENT))) landed))
       (mn (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'PRECEDES-STRICT))) landed)))
  (dk-apply! sub 'n)
  (fact 'bundle-space 'c)
  (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'n)
  (let ((o (dk-cite! 'node-sent-or-received '(BSPACE c) 'n)))
    (dk-each-leaf! (lambda () (ai o))
      (lambda ()
        (if (dk-asm? '(IS-SENT (BSPACE c) n))
            (ass)
            (let* ((ex (dk-apply! (dk-cite! 'bundle-received-sender 'c) 'n))
                   (x (dk-skolem! ex)))
              (fact 'bundle-send-nodes 'c x 'n)
              (dk-split-all!)
              (dk-apply! (dk-cite! 'bundle-send-sends 'c) x 'n)
              (fact 'sends-to-dirs '(BSPACE c) x 'n)
              (dk-split-all!)
              (dk-apply! clo x 'n)
              (fact 'bundle-send-precedes 'c x 'n)
              (ai (dk-apply! mn x))))))))
(qed 'bundle-minimal-sent)

;;; Origination, unfolded.
(define (ssl-orig-set spa u) `(SEP ssw_ (MSG-SET (TOKENS ,spa) (KEYS ,spa)) (IS-SUBTERM (TOKENS ,spa) (KEYS ,spa) ,u ssw_)))

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (ORIGINATES spa u n)
  (AND (IN n (NODES spa))
       (AND (IS-SENT spa n)
            (AND (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n))
                 (FORALL m (IMPLIES (SAME-STRAND-BEFORE spa m n)
                                    (NOT (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa m)))))))))))))))
(dk-peel!)
(mac-h 'originates '(ORIGINATES spa u n))
(let* ((ii (ssl-orig-set 'spa 'u))
       (ep `(IS-ENTRY-POINT spa n ,ii)))
  (mac-h 'is-entry-point ep)
  (dk-split-all!)
  (let ((univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SAME-STRAND-BEFORE))) "the earlier nodes")))
    (dk-conj-close!
      (lambda ()
        (cond ((dk-asm? (dk-goal)) (ass))
              ((dk-head-is? (dk-goal) 'IS-SUBTERM)
               (sep-me `(IN (NODE-CONTENT spa n) ,ii))
               (ass))
              (#t
               (dk-peel!)
               (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-asms)))))
                 (di)                                 ; u @ content(m); goal FALSITY
                 (dk-have! `(IN ,m (NODES spa))
                   (lambda () (ssl-proj! 'same-strand-before `(SAME-STRAND-BEFORE spa ,m n))))
                 (fact 'node-content-in-msgs 'spa m)
                 (dk-have! `(IN (NODE-CONTENT spa ,m) ,ii)
                   (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))
                 (ai (dk-apply! univ m)))))))))
(qed 'originates-elim)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa)
  (IMPLIES (IN n (NODES spa)) (IMPLIES (IS-SENT spa n) (IMPLIES (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n))
  (IMPLIES (FORALL m (IMPLIES (SAME-STRAND-BEFORE spa m n) (NOT (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa m)))))
    (ORIGINATES spa u n)))))))))))
(let* ((landed (dk-peel!))
       (none (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SAME-STRAND-BEFORE))) landed))
       (ii (ssl-orig-set 'spa 'u)))
  (fact 'node-content-in-msgs 'spa 'n)
  (mac 'originates)
  (mac 'is-entry-point)
  (dk-conj-close!
    (lambda ()
      (cond ((dk-asm? (dk-goal)) (ass))
            ((dk-head-is? (dk-goal) 'IN) (in-sep! (lambda () (ass)) (lambda () (ass))))
            (#t
             (dk-peel!)
             (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-asms)))))
               (di)                                     ; content(m) in I; goal FALSITY
               (sep-me `(IN (NODE-CONTENT spa ,m) ,ii))
               (ai (dk-apply! none m))))))))
(qed 'originates-intro)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (ORIGINATES spa u n)
  (AND (IS-SENT spa n) (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n))))))))))
(dk-peel!)
(fact 'originates-elim 'spa 'u 'n)
(dk-split-all!)
(dk-conj-close! (lambda () (ass)))
(qed 'originates-sent)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (FORALL m (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (ORIGINATES spa u n)
  (IMPLIES (SAME-STRAND-BEFORE spa m n) (NOT (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa m))))))))))))
(dk-peel!)
(fact 'originates-elim 'spa 'u 'n)
(dk-split-all!)
(dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SAME-STRAND-BEFORE))) "the earlier nodes") 'm)
(ass)
(qed 'originates-no-earlier)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (FORALL m (IMPLIES (UNIQUELY-ORIGINATES spa u)
  (IMPLIES (ORIGINATES spa u n) (IMPLIES (ORIGINATES spa u m) (= m n))))))))))
(dk-peel!)
(mac-h 'uniquely-originates '(UNIQUELY-ORIGINATES spa u))
(let* ((ex (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the unique originator"))
       (n0 (dk-skolem! ex))
       (all (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f n0))) "uniqueness")))
  (dk-apply! all 'n)
  (dk-apply! all 'm)
  (subst `(= m ,n0))
  (subst `(= n ,n0))
  (rfl))
(qed 'originates-unique)

;;; LEMMA 2.9: a minimal node among the bundle's nodes whose content contains u originates u.
;;; The paper's proof applies its clause 3 "as many times as necessary" to put the earlier nodes
;;; of the strand in the bundle; here that is the one closure law bundle-ssb-closed.
(sp (make-wff '(FORALL c (FORALL u (FORALL n (IMPLIES (IS-BUNDLE c) (IMPLIES (IN n (BNODES c))
  (IMPLIES (IS-SUBTERM (TOKENS (BSPACE c)) (KEYS (BSPACE c)) u (NODE-CONTENT (BSPACE c) n))
  (IMPLIES (FORALL z (IMPLIES (IN z (BNODES c)) (IMPLIES (IS-SUBTERM (TOKENS (BSPACE c)) (KEYS (BSPACE c)) u (NODE-CONTENT (BSPACE c) z))
                                                        (NOT (IN (LIST z n) (PRECEDES-STRICT c))))))
    (ORIGINATES (BSPACE c) u n))))))))))
(let* ((landed (dk-peel!))
       (mn (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'PRECEDES-STRICT))) landed))
       (spa '(BSPACE c))
       (ss `(SEP slw_ (BNODES c) (IS-SUBTERM (TOKENS ,spa) (KEYS ,spa) u (NODE-CONTENT ,spa slw_)))))
  (fact 'bundle-space 'c)
  (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'n)
  ;; Lemma 2.8 at S = the nodes whose content contains u
  (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
    (lambda () (dk-peel!) (sep-me (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) ss))) (dk-asms))) (ass)))
  (dk-have! `(FORALL x (FORALL y (IMPLIES (IN x (BNODES c)) (IMPLIES (IN y (BNODES c))
               (IMPLIES (= (NODE-CONTENT ,spa x) (NODE-CONTENT ,spa y)) (IMPLIES (IN y ,ss) (IN x ,ss)))))))
    (lambda ()
      (dk-peel!)
      (let* ((eqn (find-first (lambda (f) (and (dk-head-is? f '=) (dk-head-is? (cadr f) 'NODE-CONTENT))) (dk-asms)))
             (x (caddr (cadr eqn))) (y (caddr (caddr eqn))))
        (sep-me `(IN ,y ,ss))
        (in-sep! (lambda () (ass))
                 (lambda () (subst eqn) (ass))))))
  (dk-have! `(IN n ,ss) (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))
  (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (NOT (IN (LIST z n) (PRECEDES-STRICT c)))))
    (lambda ()
      (dk-peel!)
      (let ((z (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) ss))) (dk-asms)))))
        (sep-me `(IN ,z ,ss))
        (dk-apply! mn z)
        (ass))))
  (fact 'bundle-minimal-sent 'c ss 'n)
  ;; the entry-point conditions
  (dk-have! `(FORALL m (IMPLIES (SAME-STRAND-BEFORE ,spa m n) (NOT (IS-SUBTERM (TOKENS ,spa) (KEYS ,spa) u (NODE-CONTENT ,spa m)))))
    (lambda ()
      (dk-peel!)
      (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-asms)))))
        (di)
        (dk-apply! (dk-cite! 'bundle-ssb-closed 'c 'n) m)
        (fact 'bundle-ssb-precedes 'c m 'n)
        (ai (dk-apply! mn m)))))
  (fact 'originates-intro spa 'u 'n)
  (dk-ass!))
(qed 'bundle-minimal-originates)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing))
          '(nodes-unfold node-content-unfold node-dir-unfold directed-unfold strands-unfold index-id-unfold
            prec-strict-unfold precedes-strict-unfold precedes-unfold pair-in-power-box))
(for-each (lambda (n) (topic! n 'constructions))
          '(strand-space-parts keys-in-tokens kinv-in-fun kinv-involution kinv-injective strand-at-id node-parts node-intro node-pair-injective node-ext directed-parts
            node-step-in-directed node-content-in-msgs node-dir-cases sent-ne-received node-sent-or-received
            node-not-sent-and-received node-content-eq ssb-irreflexive ssb-transitive ssu-of-ssb ssu-refl
            ssu-cases sends-to-dirs bundle-space bundle-nodes-set bundle-send-typing
            bundle-nodes-in-space bundle-finite bundle-send-sends bundle-received-sender
            bundle-ssb-closed bundle-acyclic bundle-send-nodes ps-in-box ps-least ps-send
            ps-ssb ps-trans precedes-strict-trans precedes-strict-irreflexive bundle-send-precedes
            bundle-ssb-precedes precedes-intro-strict precedes-refl precedes-elim ps-last-step precedes-trans
            precedes-antisym precedes-set precedes-partial-order finite-strict-minimal bundle-minimal
            bundle-minimal-precedes bundle-minimal-sent originates-elim originates-intro originates-sent
            originates-no-earlier originates-unique bundle-minimal-originates))
