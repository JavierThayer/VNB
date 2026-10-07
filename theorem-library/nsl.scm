;;; nsl.scm -- THE NEEDHAM-SCHROEDER-LOWE PROTOCOL ON THE USER'S STRAND MODEL: the responder's
;;; guarantee (agreement, Proposition 5.2) and the secrecy of both nonces, the injectivity of the
;;; initiator's strand, the initiator's agreement (Propositions 5.8, 5.10, 5.13, 5.14).
;;; (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, section 5; the vocabulary is
;;;  structure-library/nsl.scm; the model is docs/strand-spaces-2026-10-06.md.)  Agent S-3,
;;;  2026-10-07.  Helper prefix: nsl-.  40 theorems, every one `modulo 0'; oracles `arith' and
;;;  `ineq' (index arithmetic through dk-nn!).
;;;
;;; NOTATION in the comments: sp = ISPACE(PK-INF(nsp)), the strand space of the NSL space nsp; T, K
;;; its tokens and keys; c(n) = NODE-CONTENT(sp, n); x @ y = IS-SUBTERM(T, K, x, y); ka = PUBKEY(nsp)(pa),
;;; kb = PUBKEY(nsp)(pb);
;;;   u0 = ENCR(LST([na, pa]), kb)    v0 = ENCR(LST([na, nb, pb]), ka)    v3 = ENCR(nb, kb).
;;;
;;; THE PLAN, and what replaces the paper's case analyses.  The paper takes the adversary's strand
;;; kinds one by one five times (Lemma 5.4, its case S, Lemma 5.12, and the two initiator
;;; propositions).  Here the case analysis is done ONCE per question, over any infiltrated space:
;;;   adversary-encr-loss    an adversary node loses an encryption it received only by decrypting
;;;                          it (D: the strand's first content is the inverse key) or by
;;;                          separating a list that contains it (S);
;;;   adversary-sent-source  what an adversary node sends was received earlier on its strand,
;;;                          unless the node builds it: M, C (from received components), E;
;;; and, on an NSL space, the regular contents are FLAT (an encryption of a non-key token or of a
;;; list of them: nsl-regular-content), whence nsl-regular-encr-subterm / -list-subterm / -no-key
;;; (the paper's three hand-waves, proved); nsl-key-secret (an uncompromised key occurs nowhere:
;;; the adversary bound); nsl-list-source (THE PAPER'S INNER ARGUMENT, the set T of Lemma 5.4's
;;; case S, proved once); nsl-adversary-loss (the two combined: an adversary node cannot lose a
;;; secret encryption except by copying a content already present earlier).  Every "minimal node
;;; is not an adversary node" step is then one citation of nsl-adversary-loss.
;;;
;;; THE STATEMENTS.  Bundles of the NSL space are written with (= (BSPACE c) sp) (S-2's
;;; convention); "C-height 3" is (IN (LIST 3 s) (BNODES c)); "Init[A, B, Na, Nb]" is a strand
;;; identifier t with IS-INIT-STRAND(nsp, STRAND-MAP(sp)(t), pa, pb, na, nb); "uniquely
;;; originating" is S-2's UNIQUELY-ORIGINATES.  The minimal node of a content-defined set is stated
;;; with the set's conjuncts curried (see section 10).  Proposition 5.13 is CORRECTED (two
;;; counterexamples, section 13); 5.13 and 5.14 carry Na /= Nb.
;;;
;;; LOAD WINDOW: immediately after theorem-library/strand-adversary-bound and the vocabulary file
;;; structure-library/nsl.scm (load.scm 3393 today: insert "structure-library/nsl" then
;;; "theorem-library/nsl").  Citations: strand-messages-laws, strand-space-laws,
;;; strand-adversary-bound (adversary-bound, flush-trace-no-sent, directed-intro), finite-surgery
;;; (nn-le-ne-succ, nn-lt-succ-le), nn-pos-is-succ, nn-order-ord (nn-le-succ-cases, nn-one-in,
;;; nn-zero-le), matof-in-mat (tuples-mono), rr basics (rr-zero-in, rr-lt-irrefl), the base theory
;;; (length-in-nn, nth-in-range, membership-implies-sethood, fun-apply-type-c).  The kit of
;;; 2026-10-07 (dk-subterm-literal!, dk-rewrite-h!, dk-nth-h!) and dk-congr!; no late tactic.

;;; -----------------------------------------------------------------------
;;; helpers (prefix nsl-)

(define nsl-sp '(ISPACE (PK-INF nsp)))
(define nsl-T '(TOKENS (ISPACE (PK-INF nsp))))
(define nsl-K '(KEYS (ISPACE (PK-INF nsp))))
(define nsl-msgs '(MSG-SET (TOKENS (ISPACE (PK-INF nsp))) (KEYS (ISPACE (PK-INF nsp)))))

(define (nsl-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(nsl-and (cdr fs)))))
(define (nsl-have-and! . fs)
  (let ((c (nsl-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
    c))

;; land CLAIM, a projection of the predicate hypothesis HYP, on a lane (HYP survives)
(define (nsl-project! pred hyp claim)
  (dk-have! claim
    (lambda ()
      (mac-h pred hyp)
      (if (not (dk-ass!))
          (begin
            (dk-split-all!)
            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-project!: not a projection" claim))))))))
  claim)

;; fact THM at ARGS unless its instance is already in context; split what landed
(define (nsl-fact-split! thm . args)
  (let ((f (apply dk-cite! thm args)))
    (if (and (pair? f) (eq? (car f) 'AND)) (dk-split-all!))
    f))

;; the index X with (IN X NN), (<= 1 X), (<= X N) in context (N a numeral): run (BODY j) with
;; (= X j) in context, for each j = 1 .. N
(define (nsl-index-cases! x n body)
  (let loop ((j 1))
    (if (= j n)
        (begin
          (dk-have! `(= ,x ,n) (lambda () (dk-nn! `(<= ,n ,x) `(<= ,x ,n))))
          (body n))
        (use-em `(= ,x ,j)
          (lambda () (body j))
          (lambda ()
            (dk-have! `(IN ,j NN) (lambda () (arith)))
            (dk-cite! 'nn-le-ne-succ j x)
            (dk-have! `(<= ,(+ j 1) ,x) (lambda () (dk-nn! `(<= (succ ,j) ,x))))
            (loop (+ j 1)))))))

;; the goal a right-nested OR of N disjuncts: select the J-th
(define (nsl-select! j n)
  (cond ((= n 1) #t)
        ((= j 1) (oi-l))
        (#t (oi-r) (nsl-select! (- j 1) (- n 1)))))

;;; -----------------------------------------------------------------------
;;; 1. THE PUBLIC-KEY SPACE, AND LITERAL THREE-ENTRY STRANDS

(sp (make-wff '(FORALL nsp (IMPLIES (IS-PK-SPACE nsp)
  (AND (IS-INFILTRATED-SPACE (PK-INF nsp))
  (AND (IS-STRAND-SPACE (ISPACE (PK-INF nsp)))
  (AND (IN (NAMES nsp) SET)
  (AND (IN (PUBKEY nsp) (FUN (NAMES nsp) (KEYS (ISPACE (PK-INF nsp)))))
  (AND (FORALL x (IMPLIES (IN x (NAMES nsp)) (IN x (TOKENS (ISPACE (PK-INF nsp))))))
  (AND (FORALL x (IMPLIES (IN x (NAMES nsp)) (NOT (IN x (KEYS (ISPACE (PK-INF nsp)))))))
       (FORALL x (FORALL y (IMPLIES (IN x (NAMES nsp)) (IMPLIES (IN y (NAMES nsp))
         (IMPLIES (= ((PUBKEY nsp) x) ((PUBKEY nsp) y)) (= x y))))))))))))))))
(dk-peel!)
(dk-have! '(IS-INFILTRATED-SPACE (PK-INF nsp))
  (lambda () (mac-h 'is-pk-space '(IS-PK-SPACE nsp)) (dk-split-all!) (dk-ass!)))
(nsl-project! 'is-infiltrated-space '(IS-INFILTRATED-SPACE (PK-INF nsp)) '(IS-STRAND-SPACE (ISPACE (PK-INF nsp))))
(mac-h 'is-pk-space '(IS-PK-SPACE nsp))
(dk-split-all!)
(dk-conj-close! (lambda () (if (not (dk-ass!)) (error "pk-space-parts: open conjunct" (dk-goal)))))
(qed 'pk-space-parts)

;; the parts of the public-key space nsp and of its strand space, landed and split
(define (nsl-space!)
  (if (not (dk-asm? '(IS-STRAND-SPACE (ISPACE (PK-INF nsp)))))
      (begin
        (fact 'pk-space-parts 'nsp)
        (dk-split-all!)
        (fact 'strand-space-parts nsl-sp)
        (dk-split-all!))))

;; a node on a strand whose trace is a literal of three entries is at index 1, 2 or 3, with the
;; entry's content and direction
(sp (make-wff '(FORALL spa (FORALL n (FORALL d1 (FORALL d2 (FORALL d3 (IMPLIES (IN n (NODES spa))
  (IMPLIES (= ((STRAND-MAP spa) (NTH 2 n)) (LIST d1 d2 d3))
    (OR (AND (= (NTH 1 n) 1) (AND (== (NODE-CONTENT spa n) (NTH 2 d1)) (== (NODE-DIR spa n) (NTH 1 d1))))
    (OR (AND (= (NTH 1 n) 2) (AND (== (NODE-CONTENT spa n) (NTH 2 d2)) (== (NODE-DIR spa n) (NTH 1 d2))))
        (AND (= (NTH 1 n) 3) (AND (== (NODE-CONTENT spa n) (NTH 2 d3)) (== (NODE-DIR spa n) (NTH 1 d3)))))))))))))))
(dk-peel!)
(let* ((sg '((STRAND-MAP spa) (NTH 2 n)))
       (lit '(LIST d1 d2 d3))
       (ds '(d1 d2 d3)))
  (fact 'node-parts 'spa 'n)
  (dk-split-all!)
  (dk-have! `(= (LENGTH ,sg) 3) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl)))
  (dk-rewrite-h! `(<= (NTH 1 n) (LENGTH ,sg)) `(LENGTH ,sg) 3)
  (nsl-index-cases! '(NTH 1 n) 3
    (lambda (j)
      (let ((dj (list-ref ds (- j 1))))
        (dk-have! `(= (NTH ,j ,sg) ,dj) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
        (fact 'node-content-eq 'spa 'n j dj)
        (dk-split-all!)
        (nsl-select! j 3)
        (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "three-strand-node: open" (dk-goal)))))))))
(qed 'three-strand-node)

;; the three nodes of a strand whose trace is a literal of three entries, with their contents
(sp (make-wff '(FORALL spa (FORALL a (FORALL d1 (FORALL d2 (FORALL d3 (IMPLIES (IN a (IDS spa))
  (IMPLIES (= ((STRAND-MAP spa) a) (LIST d1 d2 d3))
    (AND (IN (LIST 1 a) (NODES spa))
    (AND (== (NODE-CONTENT spa (LIST 1 a)) (NTH 2 d1))
    (AND (== (NODE-DIR spa (LIST 1 a)) (NTH 1 d1))
    (AND (IN (LIST 2 a) (NODES spa))
    (AND (== (NODE-CONTENT spa (LIST 2 a)) (NTH 2 d2))
    (AND (== (NODE-DIR spa (LIST 2 a)) (NTH 1 d2))
    (AND (IN (LIST 3 a) (NODES spa))
    (AND (== (NODE-CONTENT spa (LIST 3 a)) (NTH 2 d3))
         (== (NODE-DIR spa (LIST 3 a)) (NTH 1 d3)))))))))))))))))))
(dk-peel!)
(let* ((sg '((STRAND-MAP spa) a))
       (lit '(LIST d1 d2 d3))
       (ds '(d1 d2 d3)))
  (dk-have! `(= (LENGTH ,sg) 3) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl)))
  (for-each
    (lambda (j)
      (let ((dj (list-ref ds (- j 1)))
            (nj `(LIST ,j a)))
        (dk-have! `(IN ,j NN) (lambda () (arith)))
        (dk-have! `(<= 1 ,j) (lambda () (dk-nn!)))
        (dk-have! `(<= ,j (LENGTH ,sg)) (lambda () (subst `(= (LENGTH ,sg) 3)) (arith)))
        (fact 'node-intro 'spa j 'a)
        (dk-have! `(= (NTH 1 ,nj) ,j) (lambda () (nth-r) (rfl)))
        (dk-have! `(= (NTH ,j ((STRAND-MAP spa) (NTH 2 ,nj))) ,dj)
          (lambda () (nth-r) (subst `(= ,sg ,lit)) (nth-r) (rfl)))
        (fact 'node-content-eq 'spa nj j dj)
        (dk-split-all!)))
    '(1 2 3))
  (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "three-strand-nodes: open" (dk-goal))))))
(qed 'three-strand-nodes)

;;; -----------------------------------------------------------------------
;;; 2. THE REGULAR STRANDS: their traces are strands, their three nodes and contents.

(define (nsl-ka x) `((PUBKEY nsp) ,x))
(define (nsl-u0 pa pb na) `(ENCR (LST (LIST ,na ,pa)) ,(nsl-ka pb)))
(define (nsl-v0 pa pb na nb) `(ENCR (LST (LIST ,na ,nb ,pb)) ,(nsl-ka pa)))
(define (nsl-v3 pb nb) `(ENCR ,nb ,(nsl-ka pb)))
(define (nsl-dirs kind) (if (eq? kind 'init) '(SENT RECEIVED SENT) '(RECEIVED SENT RECEIVED)))
(define (nsl-trace kind pa pb na nb)
  (let ((ds (nsl-dirs kind)))
    `(LIST (LIST ,(car ds) ,(nsl-u0 pa pb na))
           (LIST ,(cadr ds) ,(nsl-v0 pa pb na nb))
           (LIST ,(caddr ds) ,(nsl-v3 pb nb)))))
(define (nsl-strand-pred kind) (if (eq? kind 'init) 'IS-INIT-STRAND 'IS-RESP-STRAND))
;; the conjuncts of IS-INIT-STRAND / IS-RESP-STRAND (structure-library/nsl.scm), in order
(define (nsl-strand-conjs kind s pa pb na nb)
  (list `(IN ,pa (NAMES nsp)) `(IN ,pb (NAMES nsp)) `(IN ,na ,nsl-T) `(IN ,nb ,nsl-T)
        (if (eq? kind 'init) `(NOT (IN ,na (NAMES nsp))) `(NOT (IN ,nb (NAMES nsp))))
        `(NOT (IN ,na ,nsl-K)) `(NOT (IN ,nb ,nsl-K))
        `(= ,s ,(nsl-trace kind pa pb na nb))))

(define nsl-names-tokens '(FORALL x (IMPLIES (IN x (NAMES nsp)) (IN x (TOKENS (ISPACE (PK-INF nsp)))))))
(define nsl-names-nonkeys '(FORALL x (IMPLIES (IN x (NAMES nsp)) (NOT (IN x (KEYS (ISPACE (PK-INF nsp))))))))
(define nsl-pubkey-inj '(FORALL x (FORALL y (IMPLIES (IN x (NAMES nsp)) (IMPLIES (IN y (NAMES nsp))
                          (IMPLIES (= ((PUBKEY nsp) x) ((PUBKEY nsp) y)) (= x y)))))))

;; a name X (IN X (NAMES nsp)) in context: land X in T, X not in K, PUBKEY(X) in K
(define (nsl-name! x)
  (if (not (dk-asm? `(IN ,x ,nsl-T))) (dk-apply! nsl-names-tokens x))
  (if (not (dk-asm? `(NOT (IN ,x ,nsl-K)))) (dk-apply! nsl-names-nonkeys x))
  (if (not (dk-asm? `(IN ,(nsl-ka x) ,nsl-K))) (fact 'fun-apply-type-c '(PUBKEY nsp) '(NAMES nsp) nsl-K x)))

;; HYP = (IS-INIT-STRAND nsp S pa pb na nb) or the responder's, in context (IS-PK-SPACE nsp and
;; the space's parts too): land its conjuncts, the typings of the names, keys and the three
;; messages; return the trace literal
(define (nsl-open-strand! hyp)
  (let* ((kind (if (eq? (car hyp) 'IS-INIT-STRAND) 'init 'resp))
         (args (cddr hyp))
         (s (car args)) (pa (cadr args)) (pb (caddr args)) (na (cadddr args)) (nb (car (cddddr args)))
         (conjs (nsl-strand-conjs kind s pa pb na nb)))
    (if (not (dk-asm? (car (last-pair conjs))))
        (begin
          (dk-have! (nsl-and conjs) (lambda () (mac-h (if (eq? kind 'init) 'is-init-strand 'is-resp-strand) hyp) (dk-ass!)))
          (dk-split-all!)))
    (nsl-name! pa)
    (nsl-name! pb)
    (dk-stl--msg! nsl-T nsl-K (nsl-u0 pa pb na))
    (dk-stl--msg! nsl-T nsl-K (nsl-v0 pa pb na nb))
    (dk-stl--msg! nsl-T nsl-K (nsl-v3 pb nb))
    (nsl-trace kind pa pb na nb)))

;; (IN (LIST dir m) (DIRECTED T K)) for m typed in MSG-SET
(define (nsl-directed! dir m)
  (fact 'directed-intro nsl-T nsl-K m)
  (dk-split-all!)
  `(IN (LIST ,dir ,m) (DIRECTED ,nsl-T ,nsl-K)))

(define (nsl-strand-stmt kind)
  `(FORALL nsp (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb (IMPLIES (IS-PK-SPACE nsp)
     (IMPLIES (,(nsl-strand-pred kind) nsp s pa pb na nb)
       (IN s (STRANDS ,nsl-T ,nsl-K)))))))))))

(define (nsl-strand-proof! kind)
  (dk-peel!)
  (nsl-space!)
  (let* ((lit (nsl-open-strand! `(,(nsl-strand-pred kind) nsp s pa pb na nb)))
         (ds (nsl-dirs kind)))
    (nsl-directed! (car ds) (nsl-u0 'pa 'pb 'na))
    (nsl-directed! (cadr ds) (nsl-v0 'pa 'pb 'na 'nb))
    (nsl-directed! (caddr ds) (nsl-v3 'pb 'nb))
    (subst `(= s ,lit))
    (mac 'STRANDS)
    (dk-each-leaf! (lambda () (ti)) (lambda () (if (not (dk-ass!)) (error "strand typing: open" (dk-goal)))))))

(sp (make-wff (nsl-strand-stmt 'init)))
(nsl-strand-proof! 'init)
(qed 'init-strand-is-strand)

(sp (make-wff (nsl-strand-stmt 'resp)))
(nsl-strand-proof! 'resp)
(qed 'resp-strand-is-strand)

;; the node facts of a regular strand: membership, direction, content
(define (nsl-nodes-stmt kind)
  (let ((ds (nsl-dirs kind)))
    `(FORALL nsp (FORALL a (FORALL pa (FORALL pb (FORALL na (FORALL nb (IMPLIES (IS-PK-SPACE nsp)
       (IMPLIES (IN a (IDS ,nsl-sp))
       (IMPLIES (,(nsl-strand-pred kind) nsp ((STRAND-MAP ,nsl-sp) a) pa pb na nb)
         ,(nsl-and
            (append-map
              (lambda (j d m)
                (list `(IN (LIST ,j a) (NODES ,nsl-sp))
                      (if (eq? d 'SENT) `(IS-SENT ,nsl-sp (LIST ,j a)) `(IS-RECEIVED ,nsl-sp (LIST ,j a)))
                      `(= (NODE-CONTENT ,nsl-sp (LIST ,j a)) ,m)))
              '(1 2 3) ds (list (nsl-u0 'pa 'pb 'na) (nsl-v0 'pa 'pb 'na 'nb) (nsl-v3 'pb 'nb)))))))))))))))

;; with (= (NTH ... ) ...) / (== ...) facts about node contents and directions in context, all
;; NTH-reduced: close a goal (= (NODE-CONTENT sp n) m), (IS-SENT sp n), (IS-RECEIVED sp n), (IN ..)
(define (nsl-eq-for lhs)
  (find-first (lambda (f) (and (pair? f) (memq (car f) '(= ==)) (equal? (cadr f) lhs) (equal? (reduce-nth-in-expr (caddr f)) (caddr f))))
              (dk-asms)))
(define (nsl-node-closer!)
  (let ((g (dk-goal)))
    (cond ((dk-ass!) #t)
          ((memq (car g) '(IS-SENT IS-RECEIVED))
           (mac (if (eq? (car g) 'IS-SENT) 'is-sent 'is-received))
           (let ((e (nsl-eq-for (cadr (dk-goal)))))
             (if (not e) (error "nsl-node-closer!: no direction equation" (dk-goal)))
             (nsl-subst-rfl! e)))
          ((eq? (car g) '=)
           (let ((e (nsl-eq-for (cadr g))))
             (if (not e) (error "nsl-node-closer!: no content equation" g))
             (nsl-subst-rfl! e)))
          (#t (error "nsl-node-closer!: cannot close" g)))))

;; subst E on the focus goal, then rfl when what is left is (= x x)
(define (nsl-subst-rfl! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (let ((g (dk-goal)))
          (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
              (rfl)
              (error "nsl-subst-rfl!: not reflexive after the rewrite" g))))))

;; reduce every NTH of a literal inside the context's == / = facts
(define (nsl-nth-all!)
  (for-each (lambda (f) (if (and (pair? f) (memq (car f) '(= ==)) (dk-contains? f 'NTH)) (dk-nth-h! f)))
            (dk-asms)))

(define (nsl-nodes-proof! kind)
  (dk-peel!)
  (nsl-space!)
  (let* ((lit (nsl-open-strand! `(,(nsl-strand-pred kind) nsp ((STRAND-MAP ,nsl-sp) a) pa pb na nb))))
    (fact 'three-strand-nodes nsl-sp 'a (cadr lit) (caddr lit) (cadddr lit))
    (dk-split-all!)
    (nsl-nth-all!)
    (dk-conj-close! nsl-node-closer!)))

(sp (make-wff (nsl-nodes-stmt 'init)))
(nsl-nodes-proof! 'init)
(qed 'init-strand-nodes)

(sp (make-wff (nsl-nodes-stmt 'resp)))
(nsl-nodes-proof! 'resp)
(qed 'resp-strand-nodes)

;;; -----------------------------------------------------------------------
;;; 3. FLAT MESSAGES.  The regular contents of NSL are encryptions of a token or of a list of
;;; tokens: what they contain is themselves, the list, and tokens.  This is the paper's "no
;;; regular node contains an encrypted term as a proper subterm" (proof of Lemma 5.6) and "no
;;; regular node contains a subterm g h where h contains any encrypted subterm" (Lemma 5.4,
;;; case S), PROVED: the inversion of the subterm relation at a flat message.

(sp (make-wff '(FORALL T (FORALL g (FORALL y (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN g SET) (IMPLIES (IN y SET)
  (NOT (IN (ENCR g y) T))))))))))
(dk-peel!)
(di)
(let ((ne (dk-cite! 'encr-ne-token 'T '(ENCR g y) 'g 'y)))
  (dk-have! '(= (ENCR g y) (ENCR g y)) (lambda () (rfl)))
  (ai ne))
(qed 'token-not-encr)

(sp (make-wff '(FORALL T (FORALL l (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN l SET) (NOT (IN (LST l) T))))))))
(dk-peel!)
(di)
(let ((ne (dk-cite! 'token-ne-list 'T '(LST l) 'l)))
  (dk-have! '(= (LST l) (LST l)) (lambda () (rfl)))
  (ai ne))
(qed 'token-not-lst)

;; an OR in context, split to its leaves (right-nested); HANDLER gets the disjunct of each leaf
(define (nsl-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (nsl-or-each! (caddr o) handler))
            (#t (handler (caddr o))))))))

;; subst E on the focus goal, then `ass' when the leaf is still open
(define (nsl-subst-ass! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (if (not (dk-ass!)) (error "nsl-subst-ass!: the rewritten goal is not in context" (dk-goal))))))

;; D inside T, and T, K sets, and D inside MSG-SET(T, K), for the flat lemmas (variables T K D)
(define (nsl-flat-setup!)
  (fact 'token-set-is-set 'T)
  (fact 'msg-set-is-set 'T 'K)
  (let ((incl (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'D) (not (dk-contains? f 'MSG-SET)))) "D inside T")))
    (dk-have! '(FORALL z (IMPLIES (IN z D) (IN z (MSG-SET T K))))
      (lambda ()
        (let ((z (cadr (car (dk-peel!)))))
          (dk-apply! incl z)
          (fact 'token-in-msgs 'T 'K z)
          (dk-ass!))))
    incl))

(sp (make-wff '(FORALL T (FORALL K (FORALL D (FORALL w (FORALL l (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (IMPLIES (FORALL x (IMPLIES (IN x D) (IN x T))) (IMPLIES (IN l (TUPLES D))
  (IMPLIES (IS-SUBTERM T K w (LST l)) (OR (= w (LST l)) (IN w D))))))))))))))
(dk-peel!)
(let ((incl (nsl-flat-setup!)))
  (dk-apply! (dk-cite! 'tuples-mono 'D '(MSG-SET T K)) 'l)
  (let ((o (dk-cite! 'subterm-of-list 'T 'K 'w 'l)))
    (nsl-or-each! o
      (lambda (d)
        (if (dk-head-is? d '=)
            (begin (oi-l) (dk-ass!))
            (let ((i (dk-skolem! d)))
              (nsl-have-and! `(IN ,i NN) '(IN l (TUPLES D)) `(<= 1 ,i) `(<= ,i (LENGTH l)))
              (fact 'nth-in-range 'D i 'l)
              (dk-apply! incl `(NTH ,i l))
              (fact 'subterm-of-token 'T 'K 'w `(NTH ,i l))
              (oi-r)
              (nsl-subst-ass! `(= w (NTH ,i l)))))))))
(qed 'subterm-of-flat-list)

(sp (make-wff '(FORALL T (FORALL K (FORALL D (FORALL w (FORALL l (FORALL ky (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (IMPLIES (FORALL x (IMPLIES (IN x D) (IN x T))) (IMPLIES (IN l (TUPLES D)) (IMPLIES (IN ky K)
  (IMPLIES (IS-SUBTERM T K w (ENCR (LST l) ky))
    (OR (= w (ENCR (LST l) ky)) (OR (= w (LST l)) (IN w D)))))))))))))))))
(dk-peel!)
(nsl-flat-setup!)
(dk-apply! (dk-cite! 'tuples-mono 'D '(MSG-SET T K)) 'l)
(fact 'list-in-msgs 'T 'K 'l)
(let ((o (dk-cite! 'subterm-of-encr 'T 'K 'w '(LST l) 'ky)))
  (nsl-or-each! o
    (lambda (d)
      (if (dk-head-is? d '=)
          (begin (oi-l) (dk-ass!))
          (begin
            (oi-r)
            (fact 'subterm-of-flat-list 'T 'K 'D 'w 'l)
            (dk-ass!))))))
(qed 'subterm-of-flat-encr-list)

(sp (make-wff '(FORALL T (FORALL K (FORALL D (FORALL w (FORALL x (FORALL ky (IMPLIES (IS-TOKEN-SET T) (IMPLIES (IN K SET)
  (IMPLIES (FORALL z (IMPLIES (IN z D) (IN z T))) (IMPLIES (IN x D) (IMPLIES (IN ky K)
  (IMPLIES (IS-SUBTERM T K w (ENCR x ky)) (OR (= w (ENCR x ky)) (IN w D))))))))))))))))
(dk-peel!)
(let ((incl (nsl-flat-setup!)))
  (dk-apply! incl 'x)
  (fact 'token-in-msgs 'T 'K 'x)
  (let ((o (dk-cite! 'subterm-of-encr 'T 'K 'w 'x 'ky)))
    (nsl-or-each! o
      (lambda (d)
        (if (dk-head-is? d '=)
            (begin (oi-l) (dk-ass!))
            (begin
              (fact 'subterm-of-token 'T 'K 'w 'x)
              (oi-r)
              (nsl-subst-ass! '(= w x))))))))
(qed 'subterm-of-flat-encr-token)

;;; -----------------------------------------------------------------------
;;; 4. THE REGULAR NODES OF AN NSL SPACE.  A regular node lies on an initiator or a responder
;;; strand (Definition 5.1), so its content is one of the three protocol messages; the content
;;; is an encryption, under a key, of a non-key token or of a list of non-key tokens.

(define nsl-D `(SEP nsd_ ,nsl-T (NOT (IN nsd_ ,nsl-K))))     ; the tokens that are not keys

(define nsl-law
  `(FORALL nli_ (IMPLIES (IN nli_ (IDS ,nsl-sp))
     (OR (IN nli_ (ADV-IDS (PK-INF nsp)))
         (OR (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
               (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) nli_) nla_ nlb_ nlm_ nln_)))))
             (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
               (IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) nli_) nla_ nlb_ nlm_ nln_))))))))))

;; IS-NSL-SPACE nsp in context: land IS-PK-SPACE, the space's parts and the strand law
(define (nsl-nsl-space!)
  (nsl-project! 'is-nsl-space '(IS-NSL-SPACE nsp) '(IS-PK-SPACE nsp))
  (nsl-space!)
  (if (not (dk-asm? nsl-law)) (nsl-project! 'is-nsl-space '(IS-NSL-SPACE nsp) nsl-law))
  nsl-law)

;; the identifier ID (in IDS) is not an adversary's: the strand at ID is an initiator's or a
;; responder's.  NOTADV is (NOT (IN ID (ADV-IDS (PK-INF nsp)))) in context.  HANDLER gets
;; (kind pa pb na nb lit) on each branch, the strand opened (nsl-open-strand!).
(define (nsl-strand-cases! id handler)
  (let ((o (dk-apply! (nsl-nsl-space!) id)))
    (nsl-or-each! o
      (lambda (d)
        (if (dk-head-is? d 'IN)
            (ai `(NOT (IN ,id (ADV-IDS (PK-INF nsp)))))
            (let* ((pa (dk-skolem! d))
                   (e2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f pa) (dk-contains? f id))) "nlb_"))
                   (pb (dk-skolem! e2))
                   (e3 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f pb) (dk-contains? f id))) "nlm_"))
                   (na (dk-skolem! e3))
                   (e4 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f na) (dk-contains? f id))) "nln_"))
                   (nb (dk-skolem! e4))
                   (hyp (dk-pick (lambda (f) (and (memq (car f) '(IS-INIT-STRAND IS-RESP-STRAND)) (dk-contains? f nb) (dk-contains? f id)))
                                 "the strand"))
                   (kind (if (eq? (car hyp) 'IS-INIT-STRAND) 'init 'resp))
                   (lit (nsl-open-strand! hyp)))
              (handler kind pa pb na nb lit)))))))

;; the regular node N (in NODES sp, IS-REGULAR-NODE in context): HANDLER gets
;; (kind j pa pb na nb) for each of the six cases, with (= (NTH 1 N) j), and the content and
;; direction of N as reduced == facts, in context
(define (nsl-regular-cases! n handler)
  (nsl-nsl-space!)
  (nsl-project! 'is-regular-node `(IS-REGULAR-NODE (PK-INF nsp) ,n) `(NOT (IN (NTH 2 ,n) (ADV-IDS (PK-INF nsp)))))
  (nsl-fact-split! 'node-parts nsl-sp n)
  (nsl-strand-cases! `(NTH 2 ,n)
    (lambda (kind pa pb na nb lit)
      (let ((o (dk-cite! 'three-strand-node nsl-sp n (cadr lit) (caddr lit) (cadddr lit))))
        (nsl-or-each! o
          (lambda (d)
            (let ((j (caddr (cadr d))))
              (dk-split-all!)
              (nsl-nth-all!)
              (handler kind j pa pb na nb))))))))

;; (IN X D) for X typed in T and not a key
(define (nsl-in-D! x)
  (dk-have! `(IN ,x ,nsl-D) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-ass!))))))

(sp (make-wff `(FORALL nsp (FORALL n (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IN n (NODES ,nsl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n)
    (FORSOME k (AND (IN k ,nsl-K)
      (OR (FORSOME x (AND (IN x ,nsl-D) (= (NODE-CONTENT ,nsl-sp n) (ENCR x k))))
          (FORSOME l (AND (IN l (TUPLES ,nsl-D)) (= (NODE-CONTENT ,nsl-sp n) (ENCR (LST l) k))))))))))))))
(dk-peel!)
(nsl-regular-cases! 'n
  (lambda (kind j pa pb na nb)
    (let* ((msg (case j ((1) (nsl-u0 pa pb na)) ((2) (nsl-v0 pa pb na nb)) (else (nsl-v3 pb nb))))
           (key (caddr msg))
           (body (cadr msg)))
      (ew key)
      (dk-conj-close!
        (lambda ()
          (if (not (dk-ass!))
              (if (= j 3)
                  (begin
                    (nsl-in-D! nb)
                    (oi-l) (ew nb)
                    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal))))))))
                  (let ((l (cadr body)))
                    (for-each nsl-in-D! (cdr l))
                    (dk-have! `(IN ,l (TUPLES ,nsl-D)) (lambda () (dk-each-leaf! (lambda () (ti)) (lambda () (dk-ass!)))))
                    (oi-r) (ew l)
                    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal)))))))))))))))
(qed 'nsl-regular-content)

;; (FORALL z (IMPLIES (IN z D) (IN z T))) for the non-key tokens D
(define nsl-D-incl `(FORALL z (IMPLIES (IN z ,nsl-D) (IN z ,nsl-T))))
(define (nsl-D-incl!)
  (dk-have! nsl-D-incl
    (lambda ()
      (let ((z (cadr (car (dk-peel!)))))
        (sep-me `(IN ,z ,nsl-D))
        (if (not (dk-ass!)) (error "nsl-D-incl!: open" (dk-goal))))))
  nsl-D-incl)

;; the content of the regular node N, by nsl-regular-content: ON-TOKEN gets (k x) with
;; (= c (ENCR x k)), (IN x D), (IN k K) in context; ON-LIST gets (k l) with (IN l (TUPLES D))
(define (nsl-rc-cases! n on-token on-list)
  (let* ((ex (dk-cite! 'nsl-regular-content 'nsp n))
         (k (dk-skolem! ex))
         (o (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f k) (dk-contains? f 'NODE-CONTENT))) "the two shapes")))
    (nsl-or-each! o
      (lambda (d)
        (if (dk-contains? d 'LST)
            (let ((l (dk-skolem! d))) (on-list k l))
            (let ((x (dk-skolem! d))) (on-token k x)))))))

;; `ai' a negation whose positive is in context: the focus leaf must close
(define (nsl-ai-close! f)
  (let ((leaf (proof-state-focus *ps*)))
    (ai f)
    (if (not (sequent-node-grounded? leaf)) (error "nsl-ai-close!: the leaf is still open after ai" f))))

;; (IN W D) in context, W an encryption, a list message or a key (in K): absurd
(define (nsl-D-absurd! w)
  (dk-landed* (lambda () (sep-me `(IN ,w ,nsl-D))))
  (cond ((dk-head-is? w 'ENCR)
         (if (not (dk-asm? `(IN ,w ,nsl-msgs))) (dk-stl--msg! nsl-T nsl-K w))
         (nsl-set! (cadr w)) (nsl-set! (caddr w))
         (nsl-ai-close! (dk-cite! 'token-not-encr nsl-T (cadr w) (caddr w))))
        ((dk-head-is? w 'LST)
         (nsl-set! (cadr w))
         (nsl-ai-close! (dk-cite! 'token-not-lst nsl-T (cadr w))))
        (#t (nsl-ai-close! `(NOT (IN ,w ,nsl-K))))))

;; land (IN TERM SET) from a typing in context, through LST / ENCR
(define (nsl-set! t)
  (let ((goal `(IN ,t SET)))
    (cond ((dk-asm? goal) goal)
          ((find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) t) (not (eq? (caddr f) 'SET)))) (dk-asms))
           => (lambda (ty) (fact 'membership-implies-sethood t (caddr ty)) goal))
          ((dk-head-is? t 'LST)
           (nsl-set! (cadr t))
           (fact 'lst-in-tuples-set (cadr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          ((dk-head-is? t 'ENCR)
           (nsl-set! (cadr t)) (nsl-set! (caddr t))
           (fact 'encr-in-tuples-set (cadr t) (caddr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          (#t (error "nsl-set!: no typing for" t)))))

;; W in T (in context) and (= W TERM) in context (either orientation), TERM an encryption or a
;; list message: absurd (the token law; TERM may contain W, so no rewriting)
(define (nsl-token-eq-absurd! w term)
  (if (not (dk-asm? `(= ,w ,term))) (dk-have! `(= ,w ,term) (lambda () (nsl-subst-rfl! `(= ,term ,w)))))
  (cond ((dk-head-is? term 'ENCR)
         (nsl-set! (cadr term)) (nsl-set! (caddr term))
         (ai (dk-cite! 'encr-ne-token nsl-T w (cadr term) (caddr term))))
        (#t
         (nsl-set! (cadr term))
         (ai (dk-cite! 'token-ne-list nsl-T w (cadr term))))))

;;; R1: an encryption inside a regular content IS the content (the paper, Lemma 5.6: "no regular
;;; node contains an encrypted term as a proper subterm").
(sp (make-wff `(FORALL nsp (FORALL n (FORALL g (FORALL y (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IN n (NODES ,nsl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN g ,nsl-msgs) (IMPLIES (IN y ,nsl-K)
  (IMPLIES (IS-SUBTERM ,nsl-T ,nsl-K (ENCR g y) (NODE-CONTENT ,nsl-sp n))
    (= (ENCR g y) (NODE-CONTENT ,nsl-sp n))))))))))))))
(dk-peel!)
(nsl-nsl-space!)
(nsl-D-incl!)
(let* ((c `(NODE-CONTENT ,nsl-sp n))
       (w '(ENCR g y))
       (hyp `(IS-SUBTERM ,nsl-T ,nsl-K ,w ,c)))
  (nsl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-token nsl-T nsl-K nsl-D w x k)
        (lambda (d)
          (if (dk-head-is? d '=) (nsl-subst-ass! `(= ,c (ENCR ,x ,k))) (nsl-D-absurd! w)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-list nsl-T nsl-K nsl-D w l k)
        (lambda (d)
          (cond ((and (dk-head-is? d '=) (dk-head-is? (caddr d) 'ENCR)) (nsl-subst-ass! `(= ,c (ENCR (LST ,l) ,k))))
                ((dk-head-is? d '=) (ai (dk-cite! 'encr-ne-list 'g 'y l)))
                (#t (nsl-D-absurd! w))))))))
(qed 'nsl-regular-encr-subterm)

;;; R2: a list message inside a regular content is a list of TOKENS (the paper, Lemma 5.4 case S:
;;; "no regular node contains a subterm g h where h contains any encrypted subterm").
(sp (make-wff `(FORALL nsp (FORALL n (FORALL m (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IN n (NODES ,nsl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN m (TUPLES ,nsl-msgs))
  (IMPLIES (IS-SUBTERM ,nsl-T ,nsl-K (LST m) (NODE-CONTENT ,nsl-sp n))
    (IN m (TUPLES ,nsl-T))))))))))))
(dk-peel!)
(nsl-nsl-space!)
(nsl-D-incl!)
(let* ((c `(NODE-CONTENT ,nsl-sp n))
       (w '(LST m))
       (hyp `(IS-SUBTERM ,nsl-T ,nsl-K ,w ,c)))
  (nsl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-token nsl-T nsl-K nsl-D w x k)
        (lambda (d)
          (if (dk-head-is? d '=) (ai (dk-cite! 'lst-ne-encr 'm x k)) (nsl-D-absurd! w)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-list nsl-T nsl-K nsl-D w l k)
        (lambda (d)
          (cond ((and (dk-head-is? d '=) (dk-head-is? (caddr d) 'ENCR)) (ai (dk-cite! 'lst-ne-encr 'm `(LST ,l) k)))
                ((dk-head-is? d '=)
                 (dk-cite! 'lst-injective 'm l)
                 (dk-apply! (dk-cite! 'tuples-mono nsl-D nsl-T) l)
                 (nsl-subst-ass! `(= m ,l)))
                (#t (nsl-D-absurd! w))))))))
(qed 'nsl-regular-list-subterm)

;;; R3: no key is a subterm of a regular content (the names and nonces are not keys, and the key
;;; of an encryption is not a subterm of it).
(sp (make-wff `(FORALL nsp (FORALL n (FORALL y (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IN n (NODES ,nsl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN y ,nsl-K)
    (NOT (IS-SUBTERM ,nsl-T ,nsl-K y (NODE-CONTENT ,nsl-sp n))))))))))))
(dk-peel!)
(di)
(nsl-nsl-space!)
(nsl-D-incl!)
(dk-apply! (dk-cite! 'keys-in-tokens nsl-sp) 'y)
(let* ((c `(NODE-CONTENT ,nsl-sp n))
       (hyp `(IS-SUBTERM ,nsl-T ,nsl-K y ,c)))
  (nsl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-token nsl-T nsl-K nsl-D 'y x k)
        (lambda (d)
          (if (dk-head-is? d '=) (nsl-token-eq-absurd! 'y (caddr d)) (nsl-D-absurd! 'y)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-list nsl-T nsl-K nsl-D 'y l k)
        (lambda (d)
          (if (dk-head-is? d '=) (nsl-token-eq-absurd! 'y (caddr d)) (nsl-D-absurd! 'y)))))))
(qed 'nsl-regular-no-key)

;;; -----------------------------------------------------------------------
;;; 5. THE ADVERSARY'S STRANDS, ONCE.  The paper takes the seven kinds of adversary strand case by
;;; case in Lemma 5.4, again in its case S (the set T), again in Lemma 5.12 and in Propositions
;;; 5.13 and 5.14.  Two lemmas over any infiltrated space say what all those case analyses use:
;;;   adversary-encr-loss    an adversary node can LOSE an encryption it received only by
;;;                          decrypting it (D: the key's inverse is then the strand's first
;;;                          content) or by separating a list that contains it (S)
;;;   adversary-sent-source  what an adversary node sends comes from an earlier node of its
;;;                          strand, unless the node BUILDS it: a known token (M), a list of
;;;                          received components (C), an encryption of a received plaintext (E)

(define nsl-asp '(ISPACE isp))
(define nsl-aT '(TOKENS (ISPACE isp)))
(define nsl-aK '(KEYS (ISPACE isp)))
(define nsl-aM '(MSG-SET (TOKENS (ISPACE isp)) (KEYS (ISPACE isp))))
(define (nsl-sg n) `((STRAND-MAP (ISPACE isp)) (NTH 2 ,n)))

;; IS-SENT asp N in context and (== (NODE-DIR asp N) RECEIVED): close the focus goal
(define (nsl-recv-absurd! n)
  (dk-have! `(= (NODE-DIR ,nsl-asp ,n) SENT) (lambda () (mac-h 'is-sent `(IS-SENT ,nsl-asp ,n)) (dk-ass!)))
  (dk-have! '(= SENT RECEIVED)
    (lambda () (subst `(= SENT (NODE-DIR ,nsl-asp ,n))) (nsl-subst-rfl! `(= (NODE-DIR ,nsl-asp ,n) RECEIVED))))
  (ai (dk-cite! 'sent-ne-received)))

;; contradictory NN premises: close the focus goal
(define (nsl-nn-absurd! . prems)
  (dk-have! '(< 0 0) (lambda () (apply dk-nn! prems)))
  (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
  (ai (dk-cite! 'rr-lt-irrefl 0)))

;; the infiltrated space isp and the adversary node M: land the space's parts, M's parts, and
;; return the disjunction of the seven trace kinds of M's strand
(define (nsl-adv-setup! m)
  (let ((h '(IS-INFILTRATED-SPACE isp)))
    (nsl-project! 'is-infiltrated-space h `(IS-STRAND-SPACE ,nsl-asp))
    (nsl-project! 'is-infiltrated-space h `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS isp)) (IN sat_ ,nsl-aT))))
    (nsl-fact-split! 'strand-space-parts nsl-asp)
    (nsl-fact-split! 'node-parts nsl-asp m)
    (fact 'strand-at-id nsl-asp `(NTH 2 ,m))
    (fact 'length-in-nn `(DIRECTED ,nsl-aT ,nsl-aK) (nsl-sg m))
    (nsl-project! 'is-adversary-node `(IS-ADVERSARY-NODE isp ,m) `(IN (NTH 2 ,m) (ADV-IDS isp)))
    (let* ((law (nsl-project! 'is-infiltrated-space h
                  `(FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS isp))
                     (IS-ADVERSARY-TRACE ,nsl-asp (ADV-TOKENS isp) ((STRAND-MAP ,nsl-asp) sap_))))))
           (tr (dk-apply! law `(NTH 2 ,m))))
      (mac-h 'is-adversary-trace tr)
      (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'IS-TEXT-TRACE))) "the seven kinds"))))

;; open the same-strand order X ==> M (kept), with X's parts
(define (nsl-ssb-open! x m)
  (nsl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,nsl-asp ,x ,m)
    `(AND (IN ,x (NODES ,nsl-asp)) (AND (IN ,m (NODES ,nsl-asp)) (AND (= (NTH 2 ,x) (NTH 2 ,m)) (< (NTH 1 ,x) (NTH 1 ,m))))))
  (dk-split-all!)
  (nsl-fact-split! 'node-parts nsl-asp x))

;; the node N = [J, NTH(2, M)] (J a term with (IN J NN), (<= 1 J), (<= J (LENGTH sigma)) in
;; context): land N in NODES and N ==> M, given (< J (NTH 1 M)) provable by dk-nn! from PREMS
(define (nsl-earlier! j m . prems)
  (let ((n `(LIST ,j (NTH 2 ,m))))
    (fact 'node-intro nsl-asp j `(NTH 2 ,m))
    (dk-have! `(SAME-STRAND-BEFORE ,nsl-asp ,n ,m)
      (lambda ()
        (mac 'same-strand-before)
        (nth-r)
        (dk-conj-close!
          (lambda ()
            (cond ((dk-ass!) #t)
                  ((dk-head-is? (dk-goal) '=) (rfl))
                  (#t (apply dk-nn! prems)))))))
    n))

;; the entry D at index K of the strand of M: with (= (NTH K sigma(NTH 2 M)) D) in context and
;; N = M, or N = [K, NTH(2, M)], or N with (= (NTH 2 N) (NTH 2 M)) and (= (NTH 1 N) K) in context:
;; land N's content and direction, reduced; return the content
(define (nsl-entry! n k d m)
  (let ((mver `(= (NTH ,k ,(nsl-sg m)) ,d))
        (nver `(= (NTH ,k ,(nsl-sg n)) ,d)))
    (if (not (dk-asm? mver)) (error "nsl-entry!: the entry is not in context" mver))
    (cond ((dk-asm? nver) #t)
          ((and (pair? n) (eq? (car n) 'LIST)) (dk-have! nver (lambda () (nth-r) (dk-ass!))))
          (#t (dk-rewrite-h! mver `(NTH 2 ,m) `(NTH 2 ,n))))
    (if (not (dk-asm? `(= (NTH 1 ,n) ,k)))
        (dk-have! `(= (NTH 1 ,n) ,k) (lambda () (if (not (equal? k `(NTH 1 ,n))) (nth-r)) (rfl))))
    (fact 'node-content-eq nsl-asp n k d)
    (dk-split-all!)
    (nsl-nth-all!)
    (nsl-content n)))

;; a literal trace LIT of three entries for M's strand ((= sigma(NTH 2 M) LIT) in context): the
;; node N of that strand (N in NODES, NTH 2 N = NTH 2 M) is at index j = 1, 2, 3: HANDLER gets j
;; with N's reduced content and direction in context
(define (nsl-lit3-cases! n m lit handler)
  (if (not (equal? n m))
      (dk-rewrite-h! `(= ,(nsl-sg m) ,lit) `(NTH 2 ,m) `(NTH 2 ,n)))
  (nsl-or-each! (dk-cite! 'three-strand-node nsl-asp n (cadr lit) (caddr lit) (cadddr lit))
    (lambda (d)
      (dk-split-all!)
      (nsl-nth-all!)
      (handler (caddr (cadr d))))))

(define (nsl-content n) (caddr (nsl-eq-for `(NODE-CONTENT ,nsl-asp ,n))))
(define (nsl-content-sp n) (caddr (nsl-eq-for `(NODE-CONTENT (ISPACE (PK-INF nsp)) ,n))))

;; W (an encryption) is a subterm of the TOKEN TK (in the space's T): absurd.  HYP is
;; (IS-SUBTERM aT aK W TK) in context.
(define (nsl-encr-in-token-absurd! w tk)
  (if (not (dk-asm? `(IN ,tk ,nsl-aT))) (error "nsl-encr-in-token-absurd!: the token is not typed" tk))
  (fact 'subterm-of-token nsl-aT nsl-aK w tk)                ; (= W TK)
  (dk-rewrite-h! `(IN ,tk ,nsl-aT) tk w)
  (nsl-set! (cadr w)) (nsl-set! (caddr w))
  (ai (dk-cite! 'token-not-encr nsl-aT (cadr w) (caddr w))))

;; land (IN ((KINV asp) K0) T) and in K
(define (nsl-kinv-typed! k0)
  (fact 'kinv-in-fun nsl-asp)
  (fact 'fun-apply-type-c `(KINV ,nsl-asp) nsl-aK nsl-aK k0)
  (dk-apply! (dk-cite! 'keys-in-tokens nsl-asp) `((KINV ,nsl-asp) ,k0)))

;; the two literal-entry facts (= (LENGTH sigma) n) and (= (NTH j sigma) dj) from (= sigma LIT)
(define (nsl-lit-facts! m lit)
  (let ((sg (nsl-sg m)) (n (length (cdr lit))))
    (dk-have! `(= (LENGTH ,sg) ,n) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl)))
    (let loop ((j 1))
      (if (<= j n)
          (begin
            (dk-have! `(= (NTH ,j ,sg) ,(list-ref lit j)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
            (loop (+ j 1)))))))

;; skolemise the trace predicate's existentials in order; return the witnesses
(define (nsl-trace-witnesses! d count)
  (let loop ((i 0) (ex d) (acc '()))
    (if (= i count)
        (reverse acc)
        (let* ((v (dk-skolem! ex))
               (nx (if (< (+ i 1) count)
                       (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f v))) "the next witness")
                       #f)))
          (loop (+ i 1) nx (cons v acc))))))

;; the S trace, node x: at 1 (the list) or at succ j (a component): either way W @ LST(l)
;; lands; the focus ends on ONE leaf (the two cases are joined by a cut of the claim)
(define (nsl-sep-x! l q univ d1)
  (let ((len `(LENGTH ,l))
        (claim `(IS-SUBTERM ,nsl-aT ,nsl-aK ,nsl-W (LST ,l))))
    (dk-have! claim
      (lambda ()
        (use-em '(= (NTH 1 x) 1)
          (lambda ()
            (nsl-entry! 'x 1 d1 'm)
            (dk-rewrite-h! nsl-H1 '(NODE-CONTENT (ISPACE isp) x) `(LST ,l))
            (dk-ass!))
          (lambda ()
            (let ((j (dk-skolem! (dk-cite! 'nn-pos-is-succ '(NTH 1 x)))))
              (dk-have! `(NOT (= ,j 0))
                (lambda ()
                  (di)
                  (dk-have! '(= (NTH 1 x) 1) (lambda () (subst `(= (NTH 1 x) (succ ,j))) (subst `(= ,j 0)) (arith)))
                  (ai '(NOT (= (NTH 1 x) 1)))))
              (fact 'nn-zero-le j)
              (fact 'nn-le-ne-succ 0 j)
              (dk-have! `(<= 1 ,j) (lambda () (dk-nn! `(<= (succ 0) ,j))))
              (fact 'nn-lt-succ-le '(NTH 1 x) '(NTH 1 m))
              (dk-have! `(<= ,j ,len)
                (lambda () (dk-nn! `(= (NTH 1 x) (succ ,j)) '(<= (succ (NTH 1 x)) (NTH 1 m)) `(= (NTH 1 m) (succ ,q)) `(<= ,q ,len))))
              (dk-apply! univ j)
              (nsl-entry! 'x `(succ ,j) `(LIST SENT (NTH ,j ,l)) 'm)
              (dk-rewrite-h! nsl-H1 '(NODE-CONTENT (ISPACE isp) x) `(NTH ,j ,l))
              (fact 'subterm-component nsl-aT nsl-aK nsl-W l j)
              (dk-ass!))))))
    claim))

;; the S trace's conclusion: [1, id] ==> m, its content LST(l), and m's content the q-th component
(define (nsl-sep-finish! l q d1)
  (let ((len `(LENGTH ,l)) (sg (nsl-sg 'm)))
    (dk-have! '(<= 1 1) (lambda () (dk-nn!)))
    (dk-have! `(<= 1 (LENGTH ,sg)) (lambda () (dk-nn! `(= (LENGTH ,sg) (succ ,len)))))
    (fact 'nn-one-in)
    (let ((n1 (nsl-earlier! 1 'm `(= (NTH 1 m) (succ ,q)) `(<= 1 ,q))))
      (nsl-entry! n1 1 d1 'm)
      (nsl-have-and! `(IN ,q NN) `(IN ,l (TUPLES ,nsl-aM)) `(<= 1 ,q) `(<= ,q ,len))
      (fact 'nth-in-range nsl-aM q l)
      (dk-conj-close!
        (lambda ()
          (if (not (dk-ass!))
              (begin
                (oi-l)
                (ew l)
                (dk-conj-close!
                  (lambda ()
                    (cond ((dk-ass!) #t)
                          ((dk-head-is? (dk-goal) '=) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal)))))
                          (#t
                           (ew q)
                           (dk-conj-close!
                             (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal))))))))))))))))))

(define nsl-W '(ENCR g y))
(define nsl-H1 `(IS-SUBTERM ,nsl-aT ,nsl-aK (ENCR g y) (NODE-CONTENT ,nsl-asp x)))
(define nsl-H2 `(NOT (IS-SUBTERM ,nsl-aT ,nsl-aK (ENCR g y) (NODE-CONTENT ,nsl-asp m))))

;; the S trace: the list L, its received node at 1, the sent node M at succ q; returns q
(define (nsl-sep-sent-index! l)
  (let* ((sg (nsl-sg 'm))
         (q (dk-skolem! (dk-cite! 'nn-pos-is-succ '(NTH 1 m)))))
    (dk-have! `(NOT (= ,q 0))
      (lambda ()
        (di)
        (dk-have! '(= (NTH 1 m) 1) (lambda () (subst `(= (NTH 1 m) (succ ,q))) (subst `(= ,q 0)) (arith)))
        (ai '(NOT (= (NTH 1 m) 1)))))
    (fact 'nn-zero-in)
    (fact 'nn-zero-le q)
    (fact 'nn-le-ne-succ 0 q)
    (dk-have! `(<= 1 ,q) (lambda () (dk-nn! `(<= (succ 0) ,q))))
    (dk-have! `(<= ,q (LENGTH ,l))
      (lambda () (dk-nn! `(<= (NTH 1 m) (LENGTH ,sg)) `(= (LENGTH ,sg) (succ (LENGTH ,l))) `(= (NTH 1 m) (succ ,q)))))
    q))

(sp (make-wff `(FORALL isp (FORALL m (FORALL x (FORALL g (FORALL y
  (IMPLIES (IS-INFILTRATED-SPACE isp) (IMPLIES (IN m (NODES ,nsl-asp)) (IMPLIES (IS-ADVERSARY-NODE isp m)
  (IMPLIES (IS-SENT ,nsl-asp m) (IMPLIES (SAME-STRAND-BEFORE ,nsl-asp x m)
  (IMPLIES (IN g ,nsl-aM) (IMPLIES (IN y ,nsl-aK)
  (IMPLIES (IS-SUBTERM ,nsl-aT ,nsl-aK (ENCR g y) (NODE-CONTENT ,nsl-asp x))
  (IMPLIES (NOT (IS-SUBTERM ,nsl-aT ,nsl-aK (ENCR g y) (NODE-CONTENT ,nsl-asp m)))
    (AND (SAME-STRAND-BEFORE ,nsl-asp (LIST 1 (NTH 2 m)) m)
         (OR (FORSOME l (AND (IN l (TUPLES ,nsl-aM)) (AND (= (NODE-CONTENT ,nsl-asp (LIST 1 (NTH 2 m))) (LST l))
               (AND (IS-SUBTERM ,nsl-aT ,nsl-aK (ENCR g y) (LST l))
                    (FORSOME q (AND (IN q NN) (AND (<= 1 q) (AND (<= q (LENGTH l)) (= (NODE-CONTENT ,nsl-asp m) (NTH q l))))))))))
             (= (NODE-CONTENT ,nsl-asp (LIST 1 (NTH 2 m))) ((KINV ,nsl-asp) y))))))))))))))))))))
(dk-peel!)
(let ((kinds (nsl-adv-setup! 'm))
      (sg (nsl-sg 'm)))
  (nsl-ssb-open! 'x 'm)
  (nsl-set! 'g) (nsl-set! 'y)
  (nsl-or-each! kinds
    (lambda (d)
      (case (car d)
        ((IS-TEXT-TRACE)
         (mac-h 'is-text-trace d)
         (let* ((a (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the text") 1)))
                (lit `(LIST (LIST SENT ,a))))
           (dk-have! `(= (LENGTH ,sg) 1) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl)))
           (dk-rewrite-h! `(<= (NTH 1 m) (LENGTH ,sg)) `(LENGTH ,sg) 1)
           (nsl-nn-absurd! '(<= 1 (NTH 1 x)) '(< (NTH 1 x) (NTH 1 m)) '(<= (NTH 1 m) 1))))
        ((IS-FLUSH-TRACE) (ai (dk-cite! 'flush-trace-no-sent nsl-asp 'm)))
        ((IS-TEE-TRACE)
         (mac-h 'is-tee-trace d)
         (let* ((g0 (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message") 1)))
                (lit `(LIST (LIST RECEIVED ,g0) (LIST SENT ,g0) (LIST SENT ,g0))))
           (nsl-lit3-cases! 'x 'm lit
             (lambda (jx)
               (nsl-lit3-cases! 'm 'm lit
                 (lambda (jm)
                   (dk-rewrite-h! nsl-H1 '(NODE-CONTENT (ISPACE isp) x) g0)
                   (ai (dk-rewrite-h! nsl-H2 '(NODE-CONTENT (ISPACE isp) m) g0))))))))
        ((IS-ENCRYPT-TRACE IS-DECRYPT-TRACE)
         (let ((enc? (eq? (car d) 'IS-ENCRYPT-TRACE)))
           (mac-h (if enc? 'is-encrypt-trace 'is-decrypt-trace) d)
           (let* ((ws (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the key") 2))
                  (k0 (car ws)) (h0 (cadr ws))
                  (lit (if enc?
                           `(LIST (LIST RECEIVED ,k0) (LIST RECEIVED ,h0) (LIST SENT (ENCR ,h0 ,k0)))
                           `(LIST (LIST RECEIVED ((KINV ,nsl-asp) ,k0)) (LIST RECEIVED (ENCR ,h0 ,k0)) (LIST SENT ,h0)))))
             (fact 'encr-in-msgs nsl-aT nsl-aK h0 k0)
             (nsl-lit-facts! 'm lit)
             (nsl-lit3-cases! 'm 'm lit
               (lambda (jm)
                 (if (< jm 3)
                     (nsl-recv-absurd! 'm)
                     (nsl-lit3-cases! 'x 'm lit
                       (lambda (jx)
                         (let ((cx (nsl-content 'x)) (cm (nsl-content 'm)))
                           (dk-rewrite-h! nsl-H1 '(NODE-CONTENT (ISPACE isp) x) cx)
                           (dk-rewrite-h! nsl-H2 '(NODE-CONTENT (ISPACE isp) m) cm)
                           (cond
                             ((= jx 3) (nsl-nn-absurd! '(= (NTH 1 x) 3) '(= (NTH 1 m) 3) '(< (NTH 1 x) (NTH 1 m))))
                             ((= jx 1)
                              (if enc?
                                  (dk-apply! (dk-cite! 'keys-in-tokens nsl-asp) k0)
                                  (nsl-kinv-typed! k0))
                              (nsl-encr-in-token-absurd! nsl-W cx))
                             (enc?
                              (fact 'subterm-encr nsl-aT nsl-aK nsl-W h0 k0)
                              (ai `(NOT (IS-SUBTERM ,nsl-aT ,nsl-aK ,nsl-W ,cm))))
                             (#t
                              (nsl-or-each! (dk-cite! 'subterm-of-encr nsl-aT nsl-aK nsl-W h0 k0)
                                (lambda (e)
                                  (if (dk-head-is? e 'IS-SUBTERM)
                                      (ai `(NOT (IS-SUBTERM ,nsl-aT ,nsl-aK ,nsl-W ,cm)))
                                      (begin
                                        (nsl-fact-split! 'encr-injective 'g 'y h0 k0)
                                        (dk-have! '(<= 1 1) (lambda () (dk-nn!)))
                                        (dk-have! `(<= 1 (LENGTH ,sg)) (lambda () (subst `(= (LENGTH ,sg) 3)) (arith)))
                                        (fact 'nn-one-in)
                                        (let ((n1 (nsl-earlier! 1 'm '(= (NTH 1 m) 3))))
                                          (nsl-kinv-typed! k0)
                                          (nsl-entry! n1 1 (cadr lit) 'm)
                                          (dk-conj-close!
                                            (lambda ()
                                              (if (not (dk-ass!))
                                                  (begin
                                                    (oi-r)
                                                    (subst `(= y ,k0))
                                                    (nsl-subst-rfl! (nsl-eq-for `(NODE-CONTENT ,nsl-asp ,n1)))))))))))))))))))))))
        ((IS-SEPARATE-TRACE)
         (mac-h 'is-separate-trace d)
         (let* ((l (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list") 1)))
                (len `(LENGTH ,l))
                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SENT) (dk-contains? f l))) "the sent entries"))
                (d1 `(LIST RECEIVED (LST ,l))))
           (fact 'length-in-nn nsl-aM l)
           (fact 'list-in-msgs nsl-aT nsl-aK l)
           (use-em '(= (NTH 1 m) 1)
             (lambda () (nsl-entry! 'm 1 d1 'm) (nsl-recv-absurd! 'm))
             (lambda ()
               (let ((q (nsl-sep-sent-index! l)))
                 (dk-apply! univ q)
                 (nsl-entry! 'm `(succ ,q) `(LIST SENT (NTH ,q ,l)) 'm)
                 (nsl-sep-x! l q univ d1)
                 (nsl-sep-finish! l q d1))))))
        ((IS-CONCAT-TRACE)
         (mac-h 'is-concat-trace d)
         (let* ((l (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list") 1)))
                (len `(LENGTH ,l))
                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'RECEIVED))) "the received entries")))
           (fact 'length-in-nn nsl-aM l)
           (dk-have! `(<= (NTH 1 m) (succ ,len))
             (lambda () (dk-nn! `(<= (NTH 1 m) (LENGTH ,sg)) `(= (LENGTH ,sg) (succ ,len)))))
           (nsl-or-each! (dk-cite! 'nn-le-succ-cases len '(NTH 1 m))
             (lambda (e)
               (if (dk-head-is? e '<=)
                   (begin
                     (dk-apply! univ '(NTH 1 m))
                     (nsl-entry! 'm '(NTH 1 m) `(LIST RECEIVED (NTH (NTH 1 m) ,l)) 'm)
                     (nsl-recv-absurd! 'm))
                   (begin
                     (nsl-entry! 'm `(succ ,len) `(LIST SENT (LST ,l)) 'm)
                     (fact 'nn-lt-succ-le '(NTH 1 x) '(NTH 1 m))
                     (dk-have! `(<= (NTH 1 x) ,len) (lambda () (dk-nn! '(<= (succ (NTH 1 x)) (NTH 1 m)) `(= (NTH 1 m) (succ ,len)))))
                     (dk-apply! univ '(NTH 1 x))
                     (dk-rewrite-h! `(= (NTH (NTH 1 x) ,sg) (LIST RECEIVED (NTH (NTH 1 x) ,l))) '(NTH 2 m) '(NTH 2 x))
                     (nsl-entry! 'x '(NTH 1 x) `(LIST RECEIVED (NTH (NTH 1 x) ,l)) 'x)
                     (dk-rewrite-h! nsl-H1 '(NODE-CONTENT (ISPACE isp) x) `(NTH (NTH 1 x) ,l))
                     (fact 'subterm-component nsl-aT nsl-aK nsl-W l '(NTH 1 x))
                     (ai (dk-rewrite-h! nsl-H2 '(NODE-CONTENT (ISPACE isp) m) `(LST ,l)))))))))
        (else (error "adversary-encr-loss: an unexpected kind" (car d)))))))
(qed 'adversary-encr-loss)

;; the typings node-intro needs for a NUMERAL index J of M's strand ((= (LENGTH sigma) N) in context)
(define (nsl-num-index! j m)
  (let* ((sg (nsl-sg m))
         (leq (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) `(LENGTH ,sg)) (number? (caddr f)))) (dk-asms))))
    (dk-have! `(IN ,j NN) (lambda () (arith)))
    (dk-have! `(<= 1 ,j) (lambda () (dk-nn!)))
    (dk-have! `(<= ,j (LENGTH ,sg)) (lambda () (subst leq) (arith)))))

;; the first disjunct of adversary-sent-source at the node [J, NTH(2, m)] whose entry D is in
;; context and whose content X has w as a subterm ((IS-SUBTERM aT aK w X) in context)
(define (nsl-src-first! j d . prems)
  (if (number? j) (nsl-num-index! j 'm))
  (let ((n1 (apply nsl-earlier! j 'm prems)))
    (nsl-entry! n1 j d 'm)
    (oi-l)
    (ew n1)
    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nsl-subst-ass! (nsl-eq-for (list-ref (dk-goal) 4))))))))

(define nsl-Hw `(IS-SUBTERM ,nsl-aT ,nsl-aK w (NODE-CONTENT ,nsl-asp m)))

(sp (make-wff `(FORALL isp (FORALL m (FORALL w
  (IMPLIES (IS-INFILTRATED-SPACE isp) (IMPLIES (IN m (NODES ,nsl-asp)) (IMPLIES (IS-ADVERSARY-NODE isp m)
  (IMPLIES (IS-SENT ,nsl-asp m) (IMPLIES (IS-SUBTERM ,nsl-aT ,nsl-aK w (NODE-CONTENT ,nsl-asp m))
    (OR (FORSOME x (AND (SAME-STRAND-BEFORE ,nsl-asp x m) (IS-SUBTERM ,nsl-aT ,nsl-aK w (NODE-CONTENT ,nsl-asp x))))
        (AND (= w (NODE-CONTENT ,nsl-asp m))
             (OR (IN w (ADV-TOKENS isp))
             (OR (FORSOME l (AND (IN l (TUPLES ,nsl-aM)) (AND (= (NODE-CONTENT ,nsl-asp m) (LST l))
                   (FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (IMPLIES (<= i (LENGTH l))
                     (FORSOME x (AND (SAME-STRAND-BEFORE ,nsl-asp x m) (= (NODE-CONTENT ,nsl-asp x) (NTH i l)))))))))))
                 (FORSOME h (FORSOME k (AND (IN k ,nsl-aK) (AND (= (NODE-CONTENT ,nsl-asp m) (ENCR h k))
                   (FORSOME x (AND (SAME-STRAND-BEFORE ,nsl-asp x m) (= (NODE-CONTENT ,nsl-asp x) h)))))))))))))))))))))
(dk-peel!)
(let ((kinds (nsl-adv-setup! 'm))
      (sg (nsl-sg 'm))
      (cm `(NODE-CONTENT ,nsl-asp m)))
  (nsl-or-each! kinds
    (lambda (d)
      (case (car d)
        ((IS-TEXT-TRACE)
         (mac-h 'is-text-trace d)
         (let* ((a (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the text") 1)))
                (lit `(LIST (LIST SENT ,a))))
           (nsl-lit-facts! 'm lit)
           (dk-rewrite-h! `(<= (NTH 1 m) (LENGTH ,sg)) `(LENGTH ,sg) 1)
           (dk-have! '(= (NTH 1 m) 1) (lambda () (dk-nn! '(<= 1 (NTH 1 m)) '(<= (NTH 1 m) 1))))
           (nsl-entry! 'm 1 (cadr lit) 'm)
           (dk-rewrite-h! nsl-Hw cm a)
           (dk-apply! `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS isp)) (IN sat_ ,nsl-aT))) a)
           (fact 'subterm-of-token nsl-aT nsl-aK 'w a)
           (oi-r)
           (dk-conj-close!
             (lambda ()
               (if (dk-head-is? (dk-goal) '=)
                   (begin (subst `(= w ,a)) (nsl-subst-rfl! (nsl-eq-for cm)))
                   (begin (oi-l) (nsl-subst-ass! `(= w ,a))))))))
        ((IS-FLUSH-TRACE) (ai (dk-cite! 'flush-trace-no-sent nsl-asp 'm)))
        ((IS-TEE-TRACE)
         (mac-h 'is-tee-trace d)
         (let* ((g0 (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message") 1)))
                (lit `(LIST (LIST RECEIVED ,g0) (LIST SENT ,g0) (LIST SENT ,g0))))
           (nsl-lit-facts! 'm lit)
           (nsl-lit3-cases! 'm 'm lit
             (lambda (jm)
               (if (= jm 1)
                   (nsl-recv-absurd! 'm)
                   (begin
                     (dk-rewrite-h! nsl-Hw cm g0)
                     (nsl-src-first! 1 (cadr lit) `(= (NTH 1 m) ,jm))))))))
        ((IS-ENCRYPT-TRACE IS-DECRYPT-TRACE)
         (let ((enc? (eq? (car d) 'IS-ENCRYPT-TRACE)))
           (mac-h (if enc? 'is-encrypt-trace 'is-decrypt-trace) d)
           (let* ((ws (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the key") 2))
                  (k0 (car ws)) (h0 (cadr ws))
                  (lit (if enc?
                           `(LIST (LIST RECEIVED ,k0) (LIST RECEIVED ,h0) (LIST SENT (ENCR ,h0 ,k0)))
                           `(LIST (LIST RECEIVED ((KINV ,nsl-asp) ,k0)) (LIST RECEIVED (ENCR ,h0 ,k0)) (LIST SENT ,h0)))))
             (fact 'encr-in-msgs nsl-aT nsl-aK h0 k0)
             (nsl-lit-facts! 'm lit)
             (nsl-lit3-cases! 'm 'm lit
               (lambda (jm)
                 (if (< jm 3)
                     (nsl-recv-absurd! 'm)
                     (let ((x2 (caddr lit)))
                       (dk-rewrite-h! nsl-Hw cm (nsl-content 'm))
                       (if enc?
                           (nsl-or-each! (dk-cite! 'subterm-of-encr nsl-aT nsl-aK 'w h0 k0)
                             (lambda (e)
                               (if (dk-head-is? e 'IS-SUBTERM)
                                   (nsl-src-first! 2 x2 '(= (NTH 1 m) 3))
                                   ;; E builds the encryption of h0, received at 2
                                   (begin
                                     (nsl-num-index! 2 'm)
                                     (let ((n2 (nsl-earlier! 2 'm '(= (NTH 1 m) 3))))
                                       (nsl-entry! n2 2 x2 'm)
                                       (oi-r)
                                       (dk-conj-close!
                                         (lambda ()
                                           (cond ((dk-head-is? (dk-goal) '=)
                                                  (subst `(= w (ENCR ,h0 ,k0))) (nsl-subst-rfl! (nsl-eq-for cm)))
                                                 (#t
                                                  (oi-r) (oi-r) (ew h0) (ew k0)
                                                  (dk-conj-close!
                                                    (lambda ()
                                                      (cond ((dk-ass!) #t)
                                                            ((dk-head-is? (dk-goal) '=) (nsl-subst-rfl! (nsl-eq-for cm)))
                                                            (#t
                                                             (ew n2)
                                                             (dk-conj-close!
                                                               (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal))))))))))))))))))))
                           (begin
                             (fact 'subterm-encr nsl-aT nsl-aK 'w h0 k0)
                             (nsl-src-first! 2 x2 '(= (NTH 1 m) 3)))))))))))
        ((IS-SEPARATE-TRACE)
         (mac-h 'is-separate-trace d)
         (let* ((l (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list") 1)))
                (len `(LENGTH ,l))
                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SENT) (dk-contains? f l))) "the sent entries"))
                (d1 `(LIST RECEIVED (LST ,l))))
           (fact 'length-in-nn nsl-aM l)
           (fact 'list-in-msgs nsl-aT nsl-aK l)
           (use-em '(= (NTH 1 m) 1)
             (lambda () (nsl-entry! 'm 1 d1 'm) (nsl-recv-absurd! 'm))
             (lambda ()
               (let ((q (nsl-sep-sent-index! l)))
                 (dk-apply! univ q)
                 (nsl-entry! 'm `(succ ,q) `(LIST SENT (NTH ,q ,l)) 'm)
                 (dk-rewrite-h! nsl-Hw cm `(NTH ,q ,l))
                 (fact 'subterm-component nsl-aT nsl-aK 'w l q)
                 (dk-have! '(<= 1 1) (lambda () (dk-nn!)))
                 (dk-have! `(<= 1 (LENGTH ,sg)) (lambda () (dk-nn! `(= (LENGTH ,sg) (succ ,len)))))
                 (fact 'nn-one-in)
                 (nsl-src-first! 1 d1 `(= (NTH 1 m) (succ ,q)) `(<= 1 ,q)))))))
        ((IS-CONCAT-TRACE)
         (mac-h 'is-concat-trace d)
         (let* ((l (car (nsl-trace-witnesses! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list") 1)))
                (len `(LENGTH ,l))
                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'RECEIVED))) "the received entries")))
           (fact 'length-in-nn nsl-aM l)
           (dk-have! `(<= (NTH 1 m) (succ ,len))
             (lambda () (dk-nn! `(<= (NTH 1 m) (LENGTH ,sg)) `(= (LENGTH ,sg) (succ ,len)))))
           (nsl-or-each! (dk-cite! 'nn-le-succ-cases len '(NTH 1 m))
             (lambda (e)
               (if (dk-head-is? e '<=)
                   (begin
                     (dk-apply! univ '(NTH 1 m))
                     (nsl-entry! 'm '(NTH 1 m) `(LIST RECEIVED (NTH (NTH 1 m) ,l)) 'm)
                     (nsl-recv-absurd! 'm))
                   (begin
                     (nsl-entry! 'm `(succ ,len) `(LIST SENT (LST ,l)) 'm)
                     (dk-rewrite-h! nsl-Hw cm `(LST ,l))
                     ;; a component i of l is the content of the received node [i, id]
                     (let ((comp! (lambda (i)
                                    (dk-have! `(<= ,i (LENGTH ,sg)) (lambda () (dk-nn! `(<= ,i ,len) `(= (LENGTH ,sg) (succ ,len)))))
                                    (dk-apply! univ i)
                                    (let ((ni (nsl-earlier! i 'm `(<= ,i ,len) `(= (NTH 1 m) (succ ,len)))))
                                      (nsl-entry! ni i `(LIST RECEIVED (NTH ,i ,l)) 'm)
                                      ni))))
                       (nsl-or-each! (dk-cite! 'subterm-of-list nsl-aT nsl-aK 'w l)
                         (lambda (f)
                           (if (dk-head-is? f '=)
                               ;; C builds the list l of components received earlier
                               (begin
                                 (oi-r)
                                 (dk-conj-close!
                                   (lambda ()
                                     (cond ((dk-head-is? (dk-goal) '=)
                                            (subst `(= w (LST ,l))) (nsl-subst-rfl! (nsl-eq-for cm)))
                                           (#t
                                            (oi-r) (oi-l) (ew l)
                                            (dk-conj-close!
                                              (lambda ()
                                                (cond ((dk-ass!) #t)
                                                      ((dk-head-is? (dk-goal) '=) (nsl-subst-rfl! (nsl-eq-for cm)))
                                                      (#t
                                                       (let* ((landed (dk-peel!))
                                                              (i (cadr (car landed))))
                                                         (let ((ni (comp! i)))
                                                           (nsl-have-and! `(IN ,i NN) `(IN ,l (TUPLES ,nsl-aM)) `(<= 1 ,i) `(<= ,i ,len))
                                                           (fact 'nth-in-range nsl-aM i l)
                                                           (ew ni)
                                                           (dk-conj-close!
                                                             (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! (nsl-eq-for (cadr (dk-goal))))))))))))))))))
                               (let ((i (dk-skolem! f)))
                                 (let ((ni (comp! i)))
                                   (oi-l)
                                   (ew ni)
                                   (dk-conj-close!
                                     (lambda () (if (not (dk-ass!)) (nsl-subst-ass! (nsl-eq-for (list-ref (dk-goal) 4))))))))))))))))))
        (else (error "adversary-sent-source: an unexpected kind" (car d)))))))
(qed 'adversary-sent-source)

;;; -----------------------------------------------------------------------
;;; 6. BUNDLE TOOLS.  A bundle c of the space spa ((= (BSPACE c) spa), the S-2 convention).

;; the send edges join bundle nodes of equal content
(sp (make-wff '(FORALL c (FORALL spa (FORALL a (FORALL b (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) spa)
  (IMPLIES (IN (LIST a b) (BSEND c))
    (AND (IN a (BNODES c)) (AND (IN b (BNODES c)) (= (NODE-CONTENT spa a) (NODE-CONTENT spa b)))))))))))))
(dk-peel!)
(nsl-fact-split! 'bundle-send-nodes 'c 'a 'b)
(dk-apply! (dk-cite! 'bundle-send-sends 'c) 'a 'b)
(nsl-fact-split! 'sends-to-dirs '(BSPACE c) 'a 'b)
(dk-rewrite-h! '(= (NODE-CONTENT (BSPACE c) a) (NODE-CONTENT (BSPACE c) b)) '(BSPACE c) 'spa)
(dk-conj-close! (lambda () (if (not (dk-ass!)) (error "bundle-send-content: open" (dk-goal)))))
(qed 'bundle-send-content)

;;; LEMMA 2.8 FOR SETS CLOSED TOWARD THE SENDER ONLY.  The paper applies its Lemma 2.8 to the set
;;; T = {m in C : m < n2, g h @ term(m)} in the S case of Lemma 5.4.  T is NOT closed under
;;; "equal terms" (the lemma's hypothesis): a node of equal term that does not precede n2 is
;;; outside T.  What the proof of 2.8 uses is weaker -- the SENDER of a member is a member -- and
;;; T has that (the sender precedes the member, hence n2).  Finding (S-3 a); this is the lemma.
(sp (make-wff '(FORALL c (FORALL S (FORALL n (IMPLIES (IS-BUNDLE c)
  (IMPLIES (FORALL z (IMPLIES (IN z S) (IN z (BNODES c))))
  (IMPLIES (FORALL x (FORALL y (IMPLIES (IN (LIST x y) (BSEND c)) (IMPLIES (IN y S) (IN x S)))))
  (IMPLIES (IN n S)
  (IMPLIES (FORALL z (IMPLIES (IN z S) (NOT (IN (LIST z n) (PRECEDES-STRICT c)))))
    (IS-SENT (BSPACE c) n)))))))))))
(let* ((landed (dk-peel!))
       (sub (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (not (dk-contains? f 'BSEND)) (not (dk-contains? f 'PRECEDES-STRICT)))) landed))
       (clo (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'BSEND))) landed))
       (mn (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'PRECEDES-STRICT))) landed)))
  (dk-apply! sub 'n)
  (fact 'bundle-space 'c)
  (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'n)
  (nsl-or-each! (dk-cite! 'node-sent-or-received '(BSPACE c) 'n)
    (lambda (d)
      (if (dk-head-is? d 'IS-SENT)
          (dk-ass!)
          (let ((x (dk-skolem! (dk-apply! (dk-cite! 'bundle-received-sender 'c) 'n))))
            (dk-apply! clo x 'n)
            (fact 'bundle-send-precedes 'c x 'n)
            (ai (dk-apply! mn x)))))))
(qed 'bundle-minimal-sent-back)

;;; THE EARLIER NODE.  n is a SENT member of S whose content holds u; u originates uniquely, at a
;;; node n0 outside S.  Then u does not originate at n, so an earlier node of n's strand -- a
;;; bundle node preceding n -- holds u.  (The step that opens Lemmas 5.4, 5.6, 5.11 and the
;;; secrecy propositions: "Nb originates uniquely at n0, n /= n0, hence ...".)
(sp (make-wff '(FORALL c (FORALL spa (FORALL S (FORALL u (FORALL n0 (FORALL n (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) spa)
  (IMPLIES (FORALL z (IMPLIES (IN z S) (IN z (BNODES c))))
  (IMPLIES (UNIQUELY-ORIGINATES spa u) (IMPLIES (ORIGINATES spa u n0) (IMPLIES (NOT (IN n0 S))
  (IMPLIES (IN n S) (IMPLIES (IS-SENT spa n) (IMPLIES (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n))
    (FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x n) (PRECEDES-STRICT c))
      (AND (SAME-STRAND-BEFORE spa x n) (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa x)))))))))))))))))))))))
(let* ((landed (dk-peel!))
       (sub (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'BNODES))) landed))
       (ex (dk-goal)))
  (dk-apply! sub 'n)
  (fact 'bundle-space 'c)
  (dk-rewrite-h! '(IS-STRAND-SPACE (BSPACE c)) '(BSPACE c) 'spa)
  (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'n)
  (dk-rewrite-h! '(IN n (NODES (BSPACE c))) '(BSPACE c) 'spa)
  (use-em ex
    (lambda () (dk-ass!))
    (lambda ()
      (let ((none `(FORALL m (IMPLIES (SAME-STRAND-BEFORE spa m n) (NOT (IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa m)))))))
        (dk-have! none
          (lambda ()
            (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-peel!)))))
              (di)
              (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,m n) (lambda () (subst '(= (BSPACE c) spa)) (dk-ass!)))
              (dk-apply! (dk-cite! 'bundle-ssb-closed 'c 'n) m)
              (fact 'bundle-ssb-precedes 'c m 'n)
              (dk-have! ex
                (lambda ()
                  (ew m)
                  (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "bundle-minimal-earlier: open" (dk-goal)))))))
              (ai `(NOT ,ex)))))
        (fact 'originates-intro 'spa 'u 'n)
        (fact 'originates-unique 'spa 'u 'n0 'n)
        (dk-rewrite-h! '(IN n S) 'n 'n0)
        (ai '(NOT (IN n0 S)))))))
(qed 'bundle-minimal-earlier)

;;; -----------------------------------------------------------------------
;;; 7. NSL: SECRET KEYS, AND THE ADVERSARY'S LOSSES.

;;; AN UNCOMPROMISED KEY NEVER APPEARS: a key y of an NSL space that the adversary does not know
;;; is a subterm of no node of any bundle.  The adversary bound (Prop. 3.3) at y; its hypothesis
;;; "y originates on no regular node" holds because no key is a subterm of a regular content
;;; (nsl-regular-no-key) -- the paper's "no initiator strand or responder strand originates K_A^-1"
;;; (Lemma 5.4, case D), which in this model is TRUE ONLY BECAUSE names and nonces are not keys.
(sp (make-wff `(FORALL nsp (FORALL c (FORALL y (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nsl-sp) (IMPLIES (IN y ,nsl-K) (IMPLIES (NOT (IN y (ADV-TOKENS (PK-INF nsp))))
    (FORALL n (IMPLIES (IN n (BNODES c)) (NOT (IS-SUBTERM ,nsl-T ,nsl-K y (NODE-CONTENT ,nsl-sp n)))))))))))))))
(let* ((landed (dk-peel!))
       (n (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BNODES c)))) landed))))
  (nsl-nsl-space!)
  (dk-apply! (dk-cite! 'keys-in-tokens nsl-sp) 'y)
  (dk-have! `(FORALL nr (IMPLIES (IN nr (BNODES c)) (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) nr) (NOT (ORIGINATES ,nsl-sp y nr)))))
    (lambda ()
      (let ((nr (cadr (find-first (lambda (f) (dk-head-is? f 'IN)) (dk-peel!)))))
        (di)
        (nsl-fact-split! 'originates-elim nsl-sp 'y nr)
        (ai (dk-cite! 'nsl-regular-no-key 'nsp nr 'y)))))
  (dk-apply! (dk-cite! 'adversary-bound '(PK-INF nsp) 'c 'y) n)
  (dk-ass!))
(qed 'nsl-key-secret)

;;; THE PAPER'S INNER ARGUMENT (Lemma 5.4, case S: the set T and its minimal member), proved once.
;;; n2 is a bundle node whose content is the q-th component of a list l of messages, l is NOT a
;;; list of tokens, and LST(l) is a subterm of the content of a node x preceding n2.  Then some
;;; bundle node z preceding n2 has n2's content.  T = {m in C : m < n2, LST(l) @ content(m)} has a
;;; minimal member m; m is sent (Lemma 2.8 in the sender-closed form above); not regular (a
;;; regular content holds only lists of tokens: nsl-regular-list-subterm); an adversary node that
;;; sends something holding LST(l) either received it earlier on its strand (against minimality)
;;; or BUILT it -- and a C node builds LST(l) from components received earlier, one of which is
;;; n2's content (adversary-sent-source).  The paper says "every member of T is a penetrator
;;; node, because no regular node contains a subterm g h where h contains any encrypted subterm";
;;; that is the regular case here, and it needs only that SOME component of l is not a token.
(sp (make-wff `(FORALL nsp (FORALL c (FORALL n2 (FORALL l (FORALL q (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nsl-sp) (IMPLIES (IN n2 (BNODES c)) (IMPLIES (IN l (TUPLES ,nsl-msgs))
  (IMPLIES (IN q NN) (IMPLIES (<= 1 q) (IMPLIES (<= q (LENGTH l))
  (IMPLIES (= (NODE-CONTENT ,nsl-sp n2) (NTH q l))
  (IMPLIES (NOT (IN l (TUPLES ,nsl-T)))
  (IMPLIES (FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x n2) (PRECEDES-STRICT c)) (IS-SUBTERM ,nsl-T ,nsl-K (LST l) (NODE-CONTENT ,nsl-sp x)))))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z n2) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,nsl-sp z) (NODE-CONTENT ,nsl-sp n2)))))))))))))))))))))))
(let* ((landed (dk-peel!))
       (ex (find-first (lambda (f) (dk-head-is? f 'FORSOME)) landed))
       (sp0 nsl-sp)
       (cond-of (lambda (v) `(AND (IN (LIST ,v n2) (PRECEDES-STRICT c)) (IS-SUBTERM ,nsl-T ,nsl-K (LST l) (NODE-CONTENT ,sp0 ,v)))))
       (tt `(SEP nst_ (BNODES c) ,(cond-of 'nst_)))
       (isp '(PK-INF nsp)))
  (nsl-nsl-space!)
  (fact 'bundle-space 'c)
  ;; T inside the bundle, nonempty, its minimal member m0
  (dk-have! `(FORALL z (IMPLIES (IN z ,tt) (IN z (BNODES c))))
    (lambda () (let ((z (cadr (car (dk-peel!))))) (sep-me `(IN ,z ,tt)) (dk-ass!))))
  (let ((x (dk-skolem! ex)))
    (dk-have! `(FORSOME w (IN w ,tt)) (lambda () (ew x) (in-sep! (lambda () (dk-ass!)) (lambda () (dk-conj-close! dk-ass!))))))
  (let* ((m0 (dk-skolem! (dk-cite! 'bundle-minimal 'c tt)))
         (minT (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f m0) (dk-contains? f 'PRECEDES-STRICT))) "m0 minimal")))
    (dk-have! `(AND (IN ,m0 (BNODES c)) ,(cond-of m0)) (lambda () (sep-me `(IN ,m0 ,tt)) (dk-split-all!) (dk-conj-close! dk-ass!)))
    (dk-split-all!)
    ;; the member z of T: closure toward the sender
    (dk-have! `(FORALL x (FORALL y (IMPLIES (IN (LIST x y) (BSEND c)) (IMPLIES (IN y ,tt) (IN x ,tt)))))
      (lambda ()
        (dk-peel!)
        (let* ((e (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BSEND c)))) (dk-asms)))
               (a (cadr (cadr e))) (b (caddr (cadr e))))
          (nsl-fact-split! 'bundle-send-content 'c sp0 a b)
          (sep-me `(IN ,b ,tt))
          (dk-split-all!)
          (fact 'bundle-send-precedes 'c a b)
          (fact 'precedes-strict-trans 'c a b 'n2)
          (dk-rewrite-h! `(IS-SUBTERM ,nsl-T ,nsl-K (LST l) (NODE-CONTENT ,sp0 ,b)) `(NODE-CONTENT ,sp0 ,b) `(NODE-CONTENT ,sp0 ,a))
          (in-sep! (lambda () (dk-ass!)) (lambda () (dk-conj-close! dk-ass!))))))
    (dk-have! `(FORALL z (IMPLIES (IN z ,tt) (NOT (IN (LIST z ,m0) (PRECEDES-STRICT c)))))
      (lambda () (let ((z (cadr (car (dk-peel!))))) (dk-apply! minT z) (dk-ass!))))
    (fact 'bundle-minimal-sent-back 'c tt m0)
    (dk-rewrite-h! `(IS-SENT (BSPACE c) ,m0) '(BSPACE c) sp0)
    (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) m0)
    (dk-rewrite-h! `(IN ,m0 (NODES (BSPACE c))) '(BSPACE c) sp0)
    (use-em `(IS-ADVERSARY-NODE ,isp ,m0)
      ;; an adversary node: it received LST(l) earlier, or built it (M, C, E)
      (lambda ()
        (nsl-or-each! (dk-cite! 'adversary-sent-source isp m0 '(LST l))
          (lambda (d)
            (if (dk-head-is? d 'FORSOME)
                (let ((x2 (dk-skolem! d)))
                  (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,x2 ,m0) (lambda () (subst `(= (BSPACE c) ,sp0)) (dk-ass!)))
                  (dk-apply! (dk-cite! 'bundle-ssb-closed 'c m0) x2)
                  (fact 'bundle-ssb-precedes 'c x2 m0)
                  (fact 'precedes-strict-trans 'c x2 m0 'n2)
                  (dk-have! `(IN ,x2 ,tt) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-conj-close! dk-ass!)))))
                  (ai (dk-apply! minT x2)))
                (begin
                  (dk-split-all!)
                  (nsl-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'ADV-TOKENS))) "the built cases")
                    (lambda (e)
                      (cond
                        ((dk-head-is? e 'IN)               ; M: a known token is not a list
                         (dk-apply! (nsl-project! 'is-infiltrated-space `(IS-INFILTRATED-SPACE ,isp)
                                      `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS ,isp)) (IN sat_ ,nsl-T))))
                                    '(LST l))
                         (nsl-set! 'l)
                         (ai (dk-cite! 'token-not-lst nsl-T 'l)))
                        ((dk-contains? e 'LST)              ; C: LST(l) = LST(l2), n2's content was received earlier
                         (let* ((l2 (dk-skolem! e))
                                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f l2))) "the components")))
                           (dk-have! `(= (LST l) (LST ,l2))
                             (lambda () (nsl-subst-ass! `(= (LST l) (NODE-CONTENT ,sp0 ,m0)))))
                           (dk-cite! 'lst-injective 'l l2)
                           (dk-have! `(<= q (LENGTH ,l2)) (lambda () (nsl-subst-ass! `(= ,l2 l))))
                           (let ((x3 (dk-skolem! (dk-apply! univ 'q))))
                             (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,x3 ,m0) (lambda () (subst `(= (BSPACE c) ,sp0)) (dk-ass!)))
                             (dk-apply! (dk-cite! 'bundle-ssb-closed 'c m0) x3)
                             (fact 'bundle-ssb-precedes 'c x3 m0)
                             (fact 'precedes-strict-trans 'c x3 m0 'n2)
                             (ew x3)
                             (dk-conj-close!
                               (lambda ()
                                 (if (not (dk-ass!))
                                     (begin
                                       (subst `(= (NODE-CONTENT ,sp0 ,x3) (NTH q ,l2)))
                                       (subst `(= (NODE-CONTENT ,sp0 n2) (NTH q l)))
                                       (subst `(= l ,l2))
                                       (fact 'length-in-nn nsl-msgs l2)
                                       (nsl-have-and! '(IN q NN) `(IN ,l2 (TUPLES ,nsl-msgs)) '(<= 1 q) `(<= q (LENGTH ,l2)))
                                       (fact 'nth-in-range nsl-msgs 'q l2)
                                       (rfl))))))))
                        (#t                                 ; E: LST(l) is not an encryption
                         (let* ((h (dk-skolem! e))
                                (e2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f h))) "the key"))
                                (k (dk-skolem! e2)))
                           (dk-have! `(= (LST l) (ENCR ,h ,k))
                             (lambda () (nsl-subst-ass! `(= (LST l) (NODE-CONTENT ,sp0 ,m0)))))
                           (ai (dk-cite! 'lst-ne-encr 'l h k))))))))))))
      ;; a regular node: LST(l) inside a regular content is a list of tokens
      (lambda ()
        (dk-have! `(IS-REGULAR-NODE ,isp ,m0)
          (lambda ()
            (mac 'is-regular-node)
            (di)
            (dk-have! `(IS-ADVERSARY-NODE ,isp ,m0) (lambda () (mac 'is-adversary-node) (dk-ass!)))
            (ai `(NOT (IS-ADVERSARY-NODE ,isp ,m0)))))
        (fact 'nsl-regular-list-subterm 'nsp m0 'l)
        (ai `(NOT (IN l (TUPLES ,nsl-T))))))))
(qed 'nsl-list-source)

;;; AN ADVERSARY NODE CANNOT LOSE A SECRET ENCRYPTION.  m is a sent adversary node of a bundle of
;;; an NSL space, an earlier node x of its strand holds ENCR(g, y), m's content does not, and the
;;; adversary does not know KINV(y).  Then a bundle node z preceding m has m's content.  (The
;;; decryption D would need KINV(y) on a bundle node: nsl-key-secret; the separation S is the
;;; inner argument: nsl-list-source.)  This is the paper's case analysis of Lemma 5.4, once.
(sp (make-wff `(FORALL nsp (FORALL c (FORALL m (FORALL x (FORALL g (FORALL y (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nsl-sp) (IMPLIES (IN m (BNODES c)) (IMPLIES (IS-ADVERSARY-NODE (PK-INF nsp) m)
  (IMPLIES (IS-SENT ,nsl-sp m) (IMPLIES (SAME-STRAND-BEFORE ,nsl-sp x m)
  (IMPLIES (IN g ,nsl-msgs) (IMPLIES (IN y ,nsl-K) (IMPLIES (NOT (IN ((KINV ,nsl-sp) y) (ADV-TOKENS (PK-INF nsp))))
  (IMPLIES (IS-SUBTERM ,nsl-T ,nsl-K (ENCR g y) (NODE-CONTENT ,nsl-sp x))
  (IMPLIES (NOT (IS-SUBTERM ,nsl-T ,nsl-K (ENCR g y) (NODE-CONTENT ,nsl-sp m)))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z m) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,nsl-sp z) (NODE-CONTENT ,nsl-sp m)))))))))))))))))))))))))
(dk-peel!)
(nsl-nsl-space!)
(fact 'bundle-space 'c)
(dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'm)
(dk-rewrite-h! '(IN m (NODES (BSPACE c))) '(BSPACE c) nsl-sp)
(fact 'adversary-encr-loss '(PK-INF nsp) 'm 'x 'g 'y)
(dk-split-all!)
(let* ((n1 '(LIST 1 (NTH 2 m)))
       (c1 `(NODE-CONTENT ,nsl-sp ,n1)))
  (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,n1 m) (lambda () (nsl-subst-ass! `(= (BSPACE c) ,nsl-sp))))
  (dk-apply! (dk-cite! 'bundle-ssb-closed 'c 'm) n1)
  (fact 'bundle-ssb-precedes 'c n1 'm)
  (nsl-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'KINV))) "S or D")
    (lambda (d)
      (if (dk-head-is? d '=)
          ;; D: the strand's first node received KINV(y), which the adversary cannot have
          (let ((kv `((KINV ,nsl-sp) y)))
            (fact 'kinv-in-fun nsl-sp)
            (fact 'fun-apply-type-c `(KINV ,nsl-sp) nsl-K nsl-K 'y)
            (dk-apply! (dk-cite! 'keys-in-tokens nsl-sp) kv)
            (fact 'token-in-msgs nsl-T nsl-K kv)
            (fact 'subterm-refl nsl-T nsl-K kv)
            (dk-have! `(IS-SUBTERM ,nsl-T ,nsl-K ,kv ,c1) (lambda () (nsl-subst-ass! `(= ,c1 ,kv))))
            (ai (dk-apply! (dk-cite! 'nsl-key-secret 'nsp 'c kv) n1)))
          ;; S: the list l of the first node holds ENCR(g, y), so not every component is a token
          (let* ((l (dk-skolem! d))
                 (q (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f l))) "the index"))))
            (fact 'length-in-nn nsl-msgs l)
            (dk-have! `(NOT (IN ,l (TUPLES ,nsl-T)))
              (lambda ()
                (di)
                (nsl-or-each! (dk-cite! 'subterm-of-list nsl-T nsl-K '(ENCR g y) l)
                  (lambda (e)
                    (if (dk-head-is? e '=)
                        (ai (dk-cite! 'encr-ne-list 'g 'y l))
                        (let ((j (dk-skolem! e)))
                          (nsl-have-and! `(IN ,j NN) `(IN ,l (TUPLES ,nsl-T)) `(<= 1 ,j) `(<= ,j (LENGTH ,l)))
                          (fact 'nth-in-range nsl-T j l)
                          (fact 'subterm-of-token nsl-T nsl-K '(ENCR g y) `(NTH ,j ,l))
                          (nsl-token-eq-absurd! `(NTH ,j ,l) '(ENCR g y))))))))
            (fact 'list-in-msgs nsl-T nsl-K l)
            (fact 'subterm-refl nsl-T nsl-K `(LST ,l))
            (dk-have! `(FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x m) (PRECEDES-STRICT c))
                          (IS-SUBTERM ,nsl-T ,nsl-K (LST ,l) (NODE-CONTENT ,nsl-sp x)))))
              (lambda ()
                (ew n1)
                (dk-conj-close! (lambda () (if (not (dk-ass!)) (nsl-subst-ass! `(= ,c1 (LST ,l))))))))
            (fact 'nsl-list-source 'nsp 'c 'm l q)
            (dk-ass!))))))
(qed 'nsl-adversary-loss)

;;; -----------------------------------------------------------------------
;;; 8. LITERAL MESSAGES: forward subterms, and disequalities.

;; does the token A occur in the literal M, as a leaf equal to A or equated to A in context?
(define (nsl-leaf-match? a x)
  (or (equal? a x) (dk-asm? `(= ,a ,x)) (dk-asm? `(= ,x ,a))))
(define (nsl-occurs? a m)
  (cond ((dk-stl--encr? m) (nsl-occurs? a (cadr m)))
        ((dk-stl--lst? m) (any-pred (lambda (mi) (nsl-occurs? a mi)) (cdr (cadr m))))
        (#t (nsl-leaf-match? a m))))

;; land (IS-SUBTERM T K A M) for a literal M in which A occurs (leaves typed)
(define (nsl-sub-fwd! a m)
  (let ((goal `(IS-SUBTERM ,nsl-T ,nsl-K ,a ,m)))
    (cond ((dk-asm? goal) goal)
          ((equal? a m)
           (dk-stl--msg! nsl-T nsl-K m)
           (fact 'subterm-refl nsl-T nsl-K m)
           goal)
          ((dk-stl--encr? m)
           (nsl-sub-fwd! a (cadr m))
           (dk-stl--msg! nsl-T nsl-K (cadr m))
           (fact 'subterm-encr nsl-T nsl-K a (cadr m) (caddr m))
           goal)
          ((dk-stl--lst? m)
           (let* ((l (cadr m))
                  (ms (cdr l))
                  (i (let loop ((ms ms) (i 1))
                       (cond ((null? ms) (error "nsl-sub-fwd!: does not occur" a m))
                             ((nsl-occurs? a (car ms)) i)
                             (#t (loop (cdr ms) (+ i 1))))))
                  (mi (list-ref ms (- i 1))))
             (nsl-sub-fwd! a mi)
             (dk-stl--tuples! nsl-T nsl-K l)
             (dk-have! `(IS-SUBTERM ,nsl-T ,nsl-K ,a (NTH ,i ,l)) (lambda () (nth-r) (dk-ass!)))
             (dk-have! `(IN ,i NN) (lambda () (arith)))
             (dk-have! `(<= 1 ,i) (lambda () (dk-nn!)))
             (dk-have! `(<= ,i (LENGTH ,l)) (lambda () (len-r) (arith)))
             (fact 'subterm-component nsl-T nsl-K a l i)
             goal))
          ((nsl-leaf-match? a m)                   ; a token leaf equated to A
           (dk-stl--msg! nsl-T nsl-K m)
           (fact 'subterm-refl nsl-T nsl-K m)
           (dk-have! goal (lambda () (nsl-subst-ass! `(= ,a ,m))))
           goal)
          (#t (error "nsl-sub-fwd!: not a literal message" m)))))

;; two literal terms A, B: are they known to differ (shape, length, or a token disequation)?
(define (nsl-distinct? a b)
  (cond ((and (dk-stl--encr? a) (dk-stl--encr? b)) (nsl-distinct? (cadr a) (cadr b)))
        ((and (dk-stl--lst? a) (dk-stl--lst? b))
         (let ((as (cdr (cadr a))) (bs (cdr (cadr b))))
           (or (not (= (length as) (length bs)))
               (let loop ((as as) (bs bs)) (and (pair? as) (or (nsl-distinct? (car as) (car bs)) (loop (cdr as) (cdr bs))))))))
        ((or (dk-stl--encr? a) (dk-stl--lst? a) (dk-stl--encr? b) (dk-stl--lst? b)) #t)
        (#t (or (dk-asm? `(NOT (= ,a ,b))) (dk-asm? `(NOT (= ,b ,a)))
                (and (dk-asm? `(IN ,a (NAMES nsp))) (dk-asm? `(NOT (IN ,b (NAMES nsp)))))
                (and (dk-asm? `(IN ,b (NAMES nsp))) (dk-asm? `(NOT (IN ,a (NAMES nsp)))))))))

;; (= A B) in context (either orientation, = or ==), A and B literal and nsl-distinct?: close the goal
(define (nsl-lit-neq! a b)
  (cond
    ((dk-asm? `(= ,b ,a)) (if (dk-asm? `(= ,a ,b)) (nsl-lit-neq-1! a b) (nsl-lit-neq-1! b a)))
    ((dk-asm? `(= ,a ,b)) (nsl-lit-neq-1! a b))
    ((or (dk-asm? `(== ,a ,b)) (dk-asm? `(== ,b ,a)))
     (dk-have! `(= ,a ,b) (lambda () (subst `(== ,a ,b)) (rfl)))
     (nsl-lit-neq-1! a b))
    (#t (error "nsl-lit-neq!: no equation in context" a b))))

(define (nsl-lit-neq-1! a b)               ; (= A B) in context
  (cond
    ((and (dk-stl--encr? a) (dk-stl--encr? b))
     (nsl-fact-split! 'encr-injective (cadr a) (caddr a) (cadr b) (caddr b))
     (nsl-lit-neq! (cadr a) (cadr b)))
    ((and (dk-stl--lst? a) (dk-stl--lst? b))
     (let ((la (cadr a)) (lb (cadr b)))
       (dk-cite! 'lst-injective la lb)
       (if (not (= (length la) (length lb)))
           (begin
             (let ((na0 (- (length la) 1)) (nb0 (- (length lb) 1)))
               (dk-congr! `(= ,la ,lb) (lambda (t) `(LENGTH ,t)) '==)
               (dk-have! `(= (LENGTH ,lb) ,na0)
                 (lambda () (subst `(== (LENGTH ,lb) (LENGTH ,la))) (len-r) (rfl)))
               (dk-have! `(= (LENGTH ,lb) ,nb0) (lambda () (len-r) (rfl)))
               (dk-rewrite-h! `(= (LENGTH ,lb) ,na0) `(LENGTH ,lb) nb0)
               (nsl-nn-absurd! `(= ,nb0 ,na0))))
           (let loop ((i 1) (as (cdr la)) (bs (cdr lb)))
             (cond ((null? as) (error "nsl-lit-neq!: the lists do not differ" la lb))
                   ((nsl-distinct? (car as) (car bs))
                    (dk-congr! `(= ,la ,lb) (lambda (t) `(NTH ,i ,t)) '==)
                    (dk-nth-h! `(== (NTH ,i ,la) (NTH ,i ,lb)))
                    (nsl-lit-neq! (car as) (car bs)))
                   (#t (loop (+ i 1) (cdr as) (cdr bs))))))))
    ((and (dk-stl--encr? a) (dk-stl--lst? b)) (ai (dk-cite! 'encr-ne-list (cadr a) (caddr a) (cadr b))))
    ((and (dk-stl--lst? a) (dk-stl--encr? b)) (ai (dk-cite! 'lst-ne-encr (cadr a) (cadr b) (caddr b))))
    ((or (dk-stl--encr? b) (dk-stl--lst? b)) (nsl-token-eq-absurd! a b))
    ((or (dk-stl--encr? a) (dk-stl--lst? a))
     (dk-have! `(= ,b ,a) (lambda () (nsl-subst-rfl! `(= ,a ,b))))
     (nsl-token-eq-absurd! b a))
    ((dk-asm? `(NOT (= ,a ,b))) (ai `(NOT (= ,a ,b))))
    ((dk-asm? `(NOT (= ,b ,a)))
     (dk-have! `(= ,b ,a) (lambda () (nsl-subst-rfl! `(= ,a ,b))))
     (ai `(NOT (= ,b ,a))))
    ((dk-asm? `(NOT (IN ,b (NAMES nsp))))
     (dk-rewrite-h! `(IN ,a (NAMES nsp)) a b)
     (ai `(NOT (IN ,b (NAMES nsp)))))
    ((dk-asm? `(NOT (IN ,a (NAMES nsp))))
     (dk-have! `(IN ,a (NAMES nsp)) (lambda () (nsl-subst-ass! `(= ,a ,b))))
     (ai `(NOT (IN ,a (NAMES nsp)))))
    (#t (error "nsl-lit-neq!: cannot tell apart" a b))))

;;; -----------------------------------------------------------------------
;;; 9. ORIGINATION ON THE REGULAR STRANDS.

;;; LEMMA 5.3: on a responder strand, Nb originates at the second node -- given Na /= Nb and
;;; Nb not a name (Definition 5.1).
(sp (make-wff `(FORALL nsp (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb (IMPLIES (IS-PK-SPACE nsp)
  (IMPLIES (IN s (IDS ,nsl-sp)) (IMPLIES (IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb)
  (IMPLIES (NOT (= na nb)) (ORIGINATES ,nsl-sp nb (LIST 2 s))))))))))))))
(dk-peel!)
(nsl-space!)
(let ((lit (nsl-open-strand! `(IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))))
  (nsl-fact-split! 'resp-strand-nodes 'nsp 's 'pa 'pb 'na 'nb)
  (nsl-sub-fwd! 'nb (nsl-v0 'pa 'pb 'na 'nb))
  (dk-have! `(IS-SUBTERM ,nsl-T ,nsl-K nb (NODE-CONTENT ,nsl-sp (LIST 2 s)))
    (lambda () (nsl-subst-ass! `(= (NODE-CONTENT ,nsl-sp (LIST 2 s)) ,(nsl-v0 'pa 'pb 'na 'nb)))))
  (dk-have! `(FORALL m (IMPLIES (SAME-STRAND-BEFORE ,nsl-sp m (LIST 2 s)) (NOT (IS-SUBTERM ,nsl-T ,nsl-K nb (NODE-CONTENT ,nsl-sp m)))))
    (lambda ()
      (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-peel!)))))
        (di)
        (nsl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,nsl-sp ,m (LIST 2 s))
          `(AND (IN ,m (NODES ,nsl-sp)) (AND (IN (LIST 2 s) (NODES ,nsl-sp)) (AND (= (NTH 2 ,m) (NTH 2 (LIST 2 s))) (< (NTH 1 ,m) (NTH 1 (LIST 2 s)))))))
        (dk-split-all!)
        (dk-nth-h! `(= (NTH 2 ,m) (NTH 2 (LIST 2 s))))
        (dk-nth-h! `(< (NTH 1 ,m) (NTH 1 (LIST 2 s))))
        (nsl-fact-split! 'node-parts nsl-sp m)
        (dk-rewrite-h! `(= ((STRAND-MAP ,nsl-sp) s) ,lit) 's `(NTH 2 ,m))
        (nsl-or-each! (dk-cite! 'three-strand-node nsl-sp m (cadr lit) (caddr lit) (cadddr lit))
          (lambda (d)
            (dk-split-all!)
            (nsl-nth-all!)
            (let ((j (caddr (cadr d))))
              (if (> j 1)
                  (nsl-nn-absurd! `(= (NTH 1 ,m) ,j) `(< (NTH 1 ,m) 2))
                  (let ((u0 (nsl-u0 'pa 'pb 'na)))
                    (dk-rewrite-h! `(IS-SUBTERM ,nsl-T ,nsl-K nb (NODE-CONTENT ,nsl-sp ,m)) `(NODE-CONTENT ,nsl-sp ,m) u0)
                    (nsl-or-each! (dk-subterm-literal! nsl-T nsl-K 'nb u0)
                      (lambda (e) (nsl-lit-neq-1! (cadr e) (caddr e))))))))))))
  (fact 'originates-intro nsl-sp 'nb '(LIST 2 s))
  (dk-ass!))
(qed 'nsl-resp-nonce-originates)

;;; On an initiator strand, Na originates at the first node (the paper, proof of Prop. 5.8: "Na
;;; cannot possibly occur earlier on t").
(sp (make-wff `(FORALL nsp (FORALL t (FORALL pa (FORALL pb (FORALL na (FORALL nb (IMPLIES (IS-PK-SPACE nsp)
  (IMPLIES (IN t (IDS ,nsl-sp)) (IMPLIES (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) t) pa pb na nb)
    (ORIGINATES ,nsl-sp na (LIST 1 t)))))))))))))
(dk-peel!)
(nsl-space!)
(nsl-open-strand! `(IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) t) pa pb na nb))
(nsl-fact-split! 'init-strand-nodes 'nsp 't 'pa 'pb 'na 'nb)
(nsl-sub-fwd! 'na (nsl-u0 'pa 'pb 'na))
(dk-have! `(IS-SUBTERM ,nsl-T ,nsl-K na (NODE-CONTENT ,nsl-sp (LIST 1 t)))
  (lambda () (nsl-subst-ass! `(= (NODE-CONTENT ,nsl-sp (LIST 1 t)) ,(nsl-u0 'pa 'pb 'na)))))
(dk-have! `(FORALL m (IMPLIES (SAME-STRAND-BEFORE ,nsl-sp m (LIST 1 t)) (NOT (IS-SUBTERM ,nsl-T ,nsl-K na (NODE-CONTENT ,nsl-sp m)))))
  (lambda ()
    (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-peel!)))))
      (di)
      (nsl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,nsl-sp ,m (LIST 1 t))
        `(AND (IN ,m (NODES ,nsl-sp)) (AND (IN (LIST 1 t) (NODES ,nsl-sp)) (AND (= (NTH 2 ,m) (NTH 2 (LIST 1 t))) (< (NTH 1 ,m) (NTH 1 (LIST 1 t)))))))
      (dk-split-all!)
      (dk-nth-h! `(< (NTH 1 ,m) (NTH 1 (LIST 1 t))))
      (nsl-fact-split! 'node-parts nsl-sp m)
      (nsl-nn-absurd! `(<= 1 (NTH 1 ,m)) `(< (NTH 1 ,m) 1)))))
(fact 'originates-intro nsl-sp 'na '(LIST 1 t))
(dk-ass!)
(qed 'nsl-init-nonce-originates)

;;; PROPOSITION 5.8 (injectivity): if Na originates uniquely, at most one initiator strand has the
;;; initiator's value Na -- whatever its names and responder's value.
(sp (make-wff `(FORALL nsp (FORALL t1 (FORALL t2 (FORALL pa (FORALL pb (FORALL na (FORALL nb (FORALL pa2 (FORALL pb2 (FORALL nb2
  (IMPLIES (IS-PK-SPACE nsp) (IMPLIES (UNIQUELY-ORIGINATES ,nsl-sp na)
  (IMPLIES (IN t1 (IDS ,nsl-sp)) (IMPLIES (IN t2 (IDS ,nsl-sp))
  (IMPLIES (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) t1) pa pb na nb)
  (IMPLIES (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) t2) pa2 pb2 na nb2)
    (= t1 t2)))))))))))))))))))
(dk-peel!)
(fact 'nsl-init-nonce-originates 'nsp 't1 'pa 'pb 'na 'nb)
(fact 'nsl-init-nonce-originates 'nsp 't2 'pa2 'pb2 'na 'nb2)
(fact 'originates-unique nsl-sp 'na '(LIST 1 t1) '(LIST 1 t2))
(nsl-fact-split! 'node-pair-injective 1 't2 1 't1)
(nsl-subst-rfl! '(= t2 t1))
(qed 'nsl-init-unique)

;;; -----------------------------------------------------------------------
;;; 10. MINIMAL NODES OF CONTENT-DEFINED SETS.  A set S = {z in C : P(content(z))}, P a list of
;;; conjuncts CONDS-OF(z); "n2 is minimal in S" is written with the conjuncts curried:
;;;   n2 in C, P(n2), and forall z in C. P(z) => not z < n2.

(define (nsl-c n) `(NODE-CONTENT ,nsl-sp ,n))
(define (nsl-sub a n) `(IS-SUBTERM ,nsl-T ,nsl-K ,a ,(nsl-c n)))
(define (nsl-S conds-of) `(SEP nsz_ (BNODES c) ,(nsl-and (conds-of 'nsz_))))
(define (nsl-min-univ conds-of n2)
  `(FORALL z (IMPLIES (IN z (BNODES c))
     ,(fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) `(NOT (IN (LIST z ,n2) (PRECEDES-STRICT c))) (conds-of 'z)))))
(define (nsl-min-conjs conds-of n2)
  (append (list `(IN ,n2 (BNODES c))) (conds-of n2) (list (nsl-min-univ conds-of n2))))

;; dk-peel!, returning the eigenvariable of the first guard (IN v _) that landed
(define (nsl-peel-var!)
  (let ((landed (dk-peel!)))
    (cadr (or (find-first (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)) (equal? (caddr f) '(BNODES c)))) landed)
              (find-first (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)
              (error "nsl-peel-var!: no guard landed" landed)))))

;; (IN Z S) from Z in C and its conjuncts in context
(define (nsl-in-S! conds-of z)
  (let ((ss (nsl-S conds-of)))
    (dk-have! `(IN ,z ,ss) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-in-S!: open" (dk-goal)))))))))))

;; open (IN Z S): land Z in C and its conjuncts
(define (nsl-open-S! conds-of z)
  (let ((ss (nsl-S conds-of)))
    (dk-have! (nsl-and (cons `(IN ,z (BNODES c)) (conds-of z)))
      (lambda () (sep-me `(IN ,z ,ss)) (dk-split-all!) (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-open-S!: open" (dk-goal)))))))
    (dk-split-all!)))

;; the minimality of N2 in S in its SEP form, from the curried universal UNIV in context
(define (nsl-minS! conds-of n2 univ)
  (let* ((ss (nsl-S conds-of))
         (f `(FORALL z (IMPLIES (IN z ,ss) (NOT (IN (LIST z ,n2) (PRECEDES-STRICT c)))))))
    (dk-have! f
      (lambda ()
        (let ((z (cadr (car (dk-peel!)))))
          (nsl-open-S! conds-of z)
          (dk-apply! univ z)
          (if (not (dk-ass!)) (error "nsl-minS!: open" (dk-goal))))))
    f))

;; N2 minimal in S (the curried universal UNIV and N2's conjuncts in context): N2 is SENT (Lemma 2.8,
;; S being closed under equal contents), and N2 is a node of the space
(define (nsl-min-sent! conds-of n2 univ)
  (let ((ss (nsl-S conds-of)))
    (fact 'bundle-space 'c)
    (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
      (lambda () (let ((z (cadr (car (dk-peel!))))) (nsl-open-S! conds-of z) (dk-ass!))))
    (dk-have! `(FORALL x (FORALL y (IMPLIES (IN x (BNODES c)) (IMPLIES (IN y (BNODES c))
                 (IMPLIES (= (NODE-CONTENT (BSPACE c) x) (NODE-CONTENT (BSPACE c) y)) (IMPLIES (IN y ,ss) (IN x ,ss)))))))
      (lambda ()
        (dk-peel!)
        (let* ((eqn (find-first (lambda (f) (and (dk-head-is? f '=) (dk-head-is? (cadr f) 'NODE-CONTENT))) (dk-asms)))
               (x (caddr (cadr eqn))) (y (caddr (caddr eqn)))
               (eq2 (dk-rewrite-h! eqn '(BSPACE c) nsl-sp)))
          (nsl-open-S! conds-of y)
          (for-each (lambda (p) (dk-rewrite-h! p (nsl-c y) (nsl-c x))) (conds-of y))
          (nsl-in-S! conds-of x))))
    (nsl-in-S! conds-of n2)
    (nsl-minS! conds-of n2 univ)
    (fact 'bundle-minimal-sent 'c ss n2)
    (dk-rewrite-h! `(IS-SENT (BSPACE c) ,n2) '(BSPACE c) nsl-sp)
    (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) n2)
    (dk-rewrite-h! `(IN ,n2 (NODES (BSPACE c))) '(BSPACE c) nsl-sp)))

;; the minimal member of S, given a member W: returns n2 with its conjuncts, the curried
;; minimality UNIV, IS-SENT, and n2 in NODES landed; returns (n2 . univ)
(define (nsl-minimal! conds-of w)
  (let ((ss (nsl-S conds-of)))
    (nsl-in-S! conds-of w)
    (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
      (lambda () (let ((z (cadr (car (dk-peel!))))) (nsl-open-S! conds-of z) (dk-ass!))))
    (dk-have! `(FORSOME w (IN w ,ss)) (lambda () (ew w) (dk-ass!)))
    (let* ((n2 (dk-skolem! (dk-cite! 'bundle-minimal 'c ss)))
           (minS (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f n2) (dk-contains? f 'PRECEDES-STRICT))) "n2 minimal"))
           (univ (nsl-min-univ conds-of n2)))
      (nsl-open-S! conds-of n2)
      (dk-have! univ
        (lambda ()
          (let ((z (nsl-peel-var!)))
            (nsl-in-S! conds-of z)
            (dk-apply! minS z)
            (if (not (dk-ass!)) (error "nsl-minimal!: open" (dk-goal))))))
      (nsl-min-sent! conds-of n2 univ)
      (cons n2 univ))))

;; with N2 minimal (UNIV in context) and X a bundle node preceding N2 ((IN (LIST X N2) PS) in
;; context): X fails one of the conjuncts.  The conjuncts are (P1 (NOT P2)), P1 holds at X:
;; land CLAIM = P2 at X, by contradiction with the minimality
(define (nsl-by-minimality! claim x univ)
  (dk-have! claim
    (lambda ()
      (use-em claim
        (lambda () (dk-ass!))
        (lambda ()
          (ai (dk-apply! univ x)))))))

;;; -----------------------------------------------------------------------
;;; 11. AGREEMENT: THE RESPONDER'S GUARANTEE (section 5.2: Lemmas 5.3, 5.4, 5.6, 5.7, Prop. 5.2).

(define nsl-isp '(PK-INF nsp))
(define (nsl-sgs n) `((STRAND-MAP ,nsl-sp) (NTH 2 ,n)))

;; the node N of a strand of sp whose trace is the literal LIT ((= sigma(NTH 2 N0) LIT) in context,
;; (= (NTH 2 N) (NTH 2 N0)) too when N /= N0): HANDLER gets the index j, N's content and direction
;; landed reduced
(define (nsl-lit3-sp! n n0 lit handler)
  (if (not (equal? n n0))
      (dk-rewrite-h! `(= ,(nsl-sgs n0) ,lit) `(NTH 2 ,n0) `(NTH 2 ,n)))
  (nsl-or-each! (dk-cite! 'three-strand-node nsl-sp n (cadr lit) (caddr lit) (cadddr lit))
    (lambda (d)
      (dk-split-all!)
      (nsl-nth-all!)
      (handler (caddr (cadr d))))))

;; IS-SENT sp N and (== (NODE-DIR sp N) RECEIVED) in context: close the goal
(define (nsl-recv-absurd-sp! n)
  (dk-have! `(= (NODE-DIR ,nsl-sp ,n) SENT) (lambda () (mac-h 'is-sent `(IS-SENT ,nsl-sp ,n)) (dk-ass!)))
  (dk-have! '(= SENT RECEIVED)
    (lambda () (subst `(= SENT (NODE-DIR ,nsl-sp ,n))) (nsl-subst-rfl! `(= (NODE-DIR ,nsl-sp ,n) RECEIVED))))
  (ai (dk-cite! 'sent-ne-received)))

;; the strand order X ==> N opened (kept), with X's parts
(define (nsl-ssb-open-sp! x n)
  (nsl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,nsl-sp ,x ,n)
    `(AND (IN ,x (NODES ,nsl-sp)) (AND (IN ,n (NODES ,nsl-sp)) (AND (= (NTH 2 ,x) (NTH 2 ,n)) (< (NTH 1 ,x) (NTH 1 ,n))))))
  (dk-split-all!)
  (nsl-fact-split! 'node-parts nsl-sp x))

;; X ==> N (opened) and N regular: X regular
(define (nsl-regular-before! x n)
  (nsl-project! 'is-regular-node `(IS-REGULAR-NODE ,nsl-isp ,n) `(NOT (IN (NTH 2 ,n) (ADV-IDS ,nsl-isp))))
  (dk-have! `(IS-REGULAR-NODE ,nsl-isp ,x)
    (lambda () (mac 'is-regular-node) (nsl-subst-ass! `(= (NTH 2 ,x) (NTH 2 ,n))))))

;; (= A B) from (= A C) or (= C A) and (== C B) / (= C B) in context, B certified
(define (nsl-eq-via! a b cterm)
  (dk-have! `(= ,a ,b)
    (lambda ()
      (let ((leaf (proof-state-focus *ps*)))
        (subst `(= ,a ,cterm))
        (if (not (sequent-node-grounded? leaf))
            (if (not (dk-ass!))
                (nsl-subst-rfl! (if (dk-asm? `(== ,cterm ,b)) `(== ,cterm ,b) `(== ,b ,cterm)))))))))

;; the statements of section 5.2: the hypotheses of Proposition 5.2
(define nsl-v0* (nsl-v0 'pa 'pb 'na 'nb))
(define nsl-v3* (nsl-v3 'pb 'nb))
(define (nsl-H-resp body)
  `(FORALL nsp (FORALL c (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb
     (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) ,nsl-sp)
     (IMPLIES (IN s (IDS ,nsl-sp)) (IMPLIES (IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb)
     (IMPLIES (IN (LIST 3 s) (BNODES c))
     (IMPLIES (NOT (IN ((KINV ,nsl-sp) ,(nsl-ka 'pa)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (= na nb)) (IMPLIES (UNIQUELY-ORIGINATES ,nsl-sp nb) ,body)))))))))))))))))
(define (nsl-conds-54 z) (list (nsl-sub 'nb z) `(NOT ,(nsl-sub nsl-v0* z))))
(define (nsl-curry fs body) (fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) body fs))

;; the responder's strand s: opened, its nodes, and n0 = [2, s] originating nb outside S
(define (nsl-resp-setup! conds-of)
  (nsl-nsl-space!)
  (nsl-open-strand! `(IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
  (nsl-fact-split! 'resp-strand-nodes 'nsp 's 'pa 'pb 'na 'nb)
  (nsl-D-incl!)
  (fact 'nsl-resp-nonce-originates 'nsp 's 'pa 'pb 'na 'nb)
  (fact 'subterm-refl nsl-T nsl-K nsl-v0*)
  (dk-have! (nsl-sub nsl-v0* '(LIST 2 s)) (lambda () (nsl-subst-ass! `(= ,(nsl-c '(LIST 2 s)) ,nsl-v0*))))
  (dk-have! `(NOT (IN (LIST 2 s) ,(nsl-S conds-of)))
    (lambda () (di) (nsl-open-S! conds-of '(LIST 2 s)) (ai `(NOT ,(nsl-sub nsl-v0* '(LIST 2 s)))))))

;;; LEMMA 5.4 (the main lemma).  S = {n in C : Nb @ content(n), v0 not @ content(n)} has a
;;; minimal node n2; it is regular and sent.  (n3 = [3, s] is in S, so S is not empty.)
(sp (make-wff (nsl-H-resp
  `(FORSOME n2 ,(nsl-and (append (nsl-min-conjs nsl-conds-54 'n2)
                                 (list `(IS-REGULAR-NODE ,nsl-isp n2) `(IS-SENT ,nsl-sp n2))))))))
(dk-peel!)
(nsl-resp-setup! nsl-conds-54)
(let* ((n3 '(LIST 3 s))
       (kb (nsl-ka 'pb)))
  (nsl-sub-fwd! 'nb nsl-v3*)
  (dk-have! (nsl-sub 'nb n3) (lambda () (nsl-subst-ass! `(= ,(nsl-c n3) ,nsl-v3*))))
  (dk-have! `(NOT ,(nsl-sub nsl-v0* n3))
    (lambda ()
      (di)
      (dk-rewrite-h! (nsl-sub nsl-v0* n3) (nsl-c n3) nsl-v3*)
      (nsl-in-D! 'nb)
      (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-token nsl-T nsl-K nsl-D nsl-v0* 'nb kb)
        (lambda (e) (if (dk-head-is? e '=) (nsl-lit-neq-1! nsl-v0* nsl-v3*) (nsl-D-absurd! nsl-v0*))))))
  (let* ((r (nsl-minimal! nsl-conds-54 n3))
         (n2 (car r)) (univ (cdr r))
         (x (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c nsl-sp (nsl-S nsl-conds-54) 'nb '(LIST 2 s) n2))))
    (nsl-by-minimality! (nsl-sub nsl-v0* x) x univ)
    (use-em `(IS-ADVERSARY-NODE ,nsl-isp ,n2)
      ;; an adversary node would lose v0 = {Na Nb B}_KA: only by decrypting (K_A^-1 is secret) or
      ;; by separating a list, which brings an earlier node of n2's content
      (lambda ()
        (let ((z (dk-skolem! (dk-cite! 'nsl-adversary-loss 'nsp 'c n2 x '(LST (LIST na nb pb)) (nsl-ka 'pa)))))
          (for-each (lambda (p) (dk-rewrite-h! p (nsl-c n2) (nsl-c z))) (nsl-conds-54 n2))
          (ai (dk-apply! univ z))))
      (lambda ()
        (dk-have! `(IS-REGULAR-NODE ,nsl-isp ,n2)
          (lambda ()
            (mac 'is-regular-node)
            (di)
            (dk-have! `(IS-ADVERSARY-NODE ,nsl-isp ,n2) (lambda () (mac 'is-adversary-node) (dk-ass!)))
            (ai `(NOT (IS-ADVERSARY-NODE ,nsl-isp ,n2)))))
        (ew n2)
        (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "lemma 5.4: open" (dk-goal)))))))))
(qed 'nsl-lemma-5-4)

;;; LEMMA 5.6: a node n1 precedes n2 on its strand, and its content is v0.  (Nb does not originate
;;; at n2, so an earlier node holds Nb; by minimality it holds v0; it is regular, and "no regular
;;; node contains an encrypted term as a proper subterm" -- nsl-regular-encr-subterm.)
(sp (make-wff (nsl-H-resp
  `(FORALL n2 ,(nsl-curry (append (nsl-min-conjs nsl-conds-54 'n2) (list `(IS-REGULAR-NODE ,nsl-isp n2) `(IS-SENT ,nsl-sp n2)))
     `(FORSOME n1 (AND (SAME-STRAND-BEFORE ,nsl-sp n1 n2) (= ,(nsl-c 'n1) ,nsl-v0*))))))))
(dk-peel!)
(nsl-resp-setup! nsl-conds-54)
(let* ((n2 'n2)
       (univ (nsl-min-univ nsl-conds-54 n2)))
  (nsl-in-S! nsl-conds-54 n2)
  (dk-have! `(FORALL z (IMPLIES (IN z ,(nsl-S nsl-conds-54)) (IN z (BNODES c))))
    (lambda () (let ((z (cadr (car (dk-peel!))))) (nsl-open-S! nsl-conds-54 z) (dk-ass!))))
  (let ((x (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c nsl-sp (nsl-S nsl-conds-54) 'nb '(LIST 2 s) n2))))
    (nsl-by-minimality! (nsl-sub nsl-v0* x) x univ)
    (nsl-ssb-open-sp! x n2)
    (nsl-regular-before! x n2)
    (fact 'nsl-regular-encr-subterm 'nsp x '(LST (LIST na nb pb)) (nsl-ka 'pa))
    (ew x)
    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nsl-subst-rfl! `(= ,nsl-v0* ,(nsl-c x))))))))
(qed 'nsl-lemma-5-6)

;;; LEMMA 5.7: the regular strand of n1 and n2 is an initiator's strand in Init[A, B, Na, Nb], and
;;; n2 is its third node.  (Read off the trace: n2 is sent after a node of content v0, which only
;;; an initiator's strand has, at its second node; the names follow from v0 BY THE INJECTIVITY OF
;;; PUBKEY -- K_A' = K_A gives A' = A -- which the paper assumes and states.)
(sp (make-wff `(FORALL nsp (FORALL n1 (FORALL n2 (FORALL pa (FORALL pb (FORALL na (FORALL nb
  (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IN pa (NAMES nsp)) (IMPLIES (IN n2 (NODES ,nsl-sp))
  (IMPLIES (IS-REGULAR-NODE ,nsl-isp n2) (IMPLIES (IS-SENT ,nsl-sp n2)
  (IMPLIES (SAME-STRAND-BEFORE ,nsl-sp n1 n2) (IMPLIES (= ,(nsl-c 'n1) ,nsl-v0*)
    (AND (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) (NTH 2 n2)) pa pb na nb) (= (NTH 1 n2) 3))))))))))))))))))
(dk-peel!)
(nsl-nsl-space!)
(nsl-ssb-open-sp! 'n1 'n2)
(nsl-fact-split! 'node-parts nsl-sp 'n2)
(nsl-project! 'is-regular-node `(IS-REGULAR-NODE ,nsl-isp n2) `(NOT (IN (NTH 2 n2) (ADV-IDS ,nsl-isp))))
(nsl-strand-cases! '(NTH 2 n2)
  (lambda (kind pa2 pb2 na2 nb2 lit)
    (nsl-lit3-sp! 'n2 'n2 lit
      (lambda (j)
        (cond
          ((and (eq? kind 'init) (= j 2)) (nsl-recv-absurd-sp! 'n2))
          ((and (eq? kind 'resp) (not (= j 2))) (nsl-recv-absurd-sp! 'n2))
          ((= j 1) (nsl-nn-absurd! '(= (NTH 1 n2) 1) '(< (NTH 1 n1) (NTH 1 n2)) '(<= 1 (NTH 1 n1))))
          (#t
           (nsl-lit3-sp! 'n1 'n2 lit
             (lambda (j1)
               (cond
                 ((>= j1 j) (nsl-nn-absurd! `(= (NTH 1 n2) ,j) `(= (NTH 1 n1) ,j1) '(< (NTH 1 n1) (NTH 1 n2))))
                 (#t
                  (let ((m1 (nsl-content-sp 'n1)))
                    (nsl-eq-via! m1 nsl-v0* (nsl-c 'n1))
                    (if (and (eq? kind 'init) (= j1 2))
                        ;; {Na' Nb' B'}_KA' = {Na Nb B}_KA
                        (let ((l2 (cadr (cadr m1))) (l0 '(LIST na nb pb)))
                          (nsl-fact-split! 'encr-injective (cadr m1) (caddr m1) (cadr nsl-v0*) (caddr nsl-v0*))
                          (dk-cite! 'lst-injective l2 l0)
                          (for-each
                            (lambda (i)
                              (dk-congr! `(= ,l2 ,l0) (lambda (t) `(NTH ,i ,t)) '==)
                              (let ((e (dk-nth-h! `(== (NTH ,i ,l2) (NTH ,i ,l0)))))
                                (dk-have! `(= ,(cadr e) ,(caddr e)) (lambda () (nsl-subst-rfl! e)))))
                            '(1 2 3))
                          (dk-apply! nsl-pubkey-inj pa2 'pa)
                          (let* ((h0 `(IS-INIT-STRAND nsp ,(nsl-sgs 'n2) ,pa2 ,pb2 ,na2 ,nb2))
                                 (h1 (dk-rewrite-h! h0 pa2 'pa))
                                 (h2 (dk-rewrite-h! h1 pb2 'pb))
                                 (h3 (dk-rewrite-h! h2 na2 'na))
                                 (h4 (dk-rewrite-h! h3 nb2 'nb)))
                            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "lemma 5.7: open" (dk-goal)))))))
                        (nsl-lit-neq-1! m1 nsl-v0*)))))))))))))
(qed 'nsl-lemma-5-7)

;;; PROPOSITION 5.2 (the responder's guarantee): C contains an initiator's strand t in
;;; Init[A, B, Na, Nb] with C-height 3.
(sp (make-wff (nsl-H-resp
  `(FORSOME t (AND (IN t (IDS ,nsl-sp)) (AND (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) t) pa pb na nb)
                                             (IN (LIST 3 t) (BNODES c))))))))
(dk-peel!)
(nsl-nsl-space!)
(nsl-open-strand! `(IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
(let* ((n2 (dk-skolem! (dk-cite! 'nsl-lemma-5-4 'nsp 'c 's 'pa 'pb 'na 'nb)))
       (n1 (dk-skolem! (dk-cite! 'nsl-lemma-5-6 'nsp 'c 's 'pa 'pb 'na 'nb n2))))
  (fact 'bundle-space 'c)
  (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) n2)
  (dk-rewrite-h! `(IN ,n2 (NODES (BSPACE c))) '(BSPACE c) nsl-sp)
  (nsl-fact-split! 'nsl-lemma-5-7 'nsp n1 n2 'pa 'pb 'na 'nb)
  (nsl-fact-split! 'node-parts nsl-sp n2)
  (let* ((e1 (dk-rewrite-h! `(= ,n2 (LIST (NTH 1 ,n2) (NTH 2 ,n2))) `(NTH 1 ,n2) 3)))
    (dk-have! `(IN (LIST 3 (NTH 2 ,n2)) (BNODES c)) (lambda () (nsl-subst-ass! `(= (LIST 3 (NTH 2 ,n2)) ,n2))))
    (ew `(NTH 2 ,n2))
    (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "prop 5.2: open" (dk-goal)))))))
(qed 'nsl-responder-agreement)

;;; -----------------------------------------------------------------------
;;; 12. SECRECY OF THE RESPONDER'S NONCE (section 5.4: Lemmas 5.11, 5.12, Prop. 5.10).

(define (nsl-or fs) (if (null? (cdr fs)) (car fs) `(OR ,(car fs) ,(nsl-or (cdr fs)))))

;; (IN L (TUPLES D)) for a literal list of non-key tokens
(define (nsl-tuples-D! l)
  (for-each nsl-in-D! (cdr l))
  (dk-have! `(IN ,l (TUPLES ,nsl-D)) (lambda () (dk-each-leaf! (lambda () (ti)) (lambda () (dk-ass!))))))

;; (IS-SUBTERM T K W M) in context, W an encryption, M a regular message (an encryption of a
;; non-key token or of a list of them): close the goal, calling ON-EQ when W = M (in context)
(define (nsl-flat-cases! w m on-eq)
  (let ((body (cadr m)) (k (caddr m)))
    (if (dk-stl--lst? body)
        (let ((l (cadr body)))
          (nsl-tuples-D! l)
          (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-list nsl-T nsl-K nsl-D w l k)
            (lambda (e)
              (cond ((and (dk-head-is? e '=) (dk-head-is? (caddr e) 'ENCR)) (on-eq))
                    ((dk-head-is? e '=) (ai (dk-cite! 'encr-ne-list (cadr w) (caddr w) l)))
                    (#t (nsl-D-absurd! w))))))
        (begin
          (nsl-in-D! body)
          (nsl-or-each! (dk-cite! 'subterm-of-flat-encr-token nsl-T nsl-K nsl-D w body k)
            (lambda (e) (if (dk-head-is? e '=) (on-eq) (nsl-D-absurd! w))))))))

;; land (NOT (IS-SUBTERM T K W (content N))) where N's content is the regular message M and W is
;; distinct from M
(define (nsl-not-sub-node! w n m)
  (dk-have! `(NOT ,(nsl-sub w n))
    (lambda ()
      (di)
      (dk-rewrite-h! (nsl-sub w n) (nsl-c n) m)
      (nsl-flat-cases! w m (lambda () (nsl-lit-neq-1! w m))))))

;; land (IS-SUBTERM T K A (content N)) where N's content is the literal M holding A
(define (nsl-sub-node! a n m)
  (nsl-sub-fwd! a m)
  (dk-have! (nsl-sub a n) (lambda () (nsl-subst-ass! `(= ,(nsl-c n) ,m)))))

;; N2 minimal (UNIV) and X a bundle node preceding it holding the first conjunct: land
;; (OR P1 P2 ...), the positives of the other conjuncts (NOT Pi), by minimality
(define (nsl-min-or! ps x univ)
  (let ((claim (nsl-or ps)) (n (length ps)))
    (dk-have! claim
      (lambda ()
        (let loop ((cs ps) (sel 1))
          (if (null? cs)
              (ai (dk-apply! univ x))
              (use-em (car cs)
                (lambda () (nsl-select! sel n) (dk-ass!))
                (lambda () (loop (cdr cs) (+ sel 1))))))))
    claim))

;; the node [J, NTH(2, N)] precedes N on its strand: N in NODES, [J, ..] in NODES and the index
;; facts in context; land its bundle membership and precedence (N in C)
(define (nsl-before-in-bundle! j n . prems)
  (let ((nj `(LIST ,j (NTH 2 ,n))))
    (dk-have! `(SAME-STRAND-BEFORE ,nsl-sp ,nj ,n)
      (lambda ()
        (mac 'same-strand-before)
        (nth-r)
        (dk-conj-close!
          (lambda ()
            (cond ((dk-ass!) #t)
                  ((dk-head-is? (dk-goal) '=) (rfl))
                  (#t (apply dk-nn! prems)))))))
    (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,nj ,n) (lambda () (nsl-subst-ass! `(= (BSPACE c) ,nsl-sp))))
    (dk-apply! (dk-cite! 'bundle-ssb-closed 'c n) nj)
    (fact 'bundle-ssb-precedes 'c nj n)
    nj))

;; ORIGINATES sp U at N2 (in context, as (ORIGINATES sp U (LIST J (NTH 2 N2))) with (= (NTH 1 N2) J)),
;; U uniquely originating at N0 outside S, N2 in S: close the goal
(define (nsl-orig-absurd! u n2 j n0 conds-of)
  (let ((nj `(LIST ,j (NTH 2 ,n2))))
    (if (not (dk-asm? `(= ,n2 ,nj)))
        (dk-rewrite-h! `(= ,n2 (LIST (NTH 1 ,n2) (NTH 2 ,n2))) `(NTH 1 ,n2) j))
    (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,u ,nj) nj n2)
    (fact 'originates-unique nsl-sp u n0 n2)
    (dk-rewrite-h! `(IN ,n2 ,(nsl-S conds-of)) n2 n0)
    (ai `(NOT (IN ,n0 ,(nsl-S conds-of))))))

(define (nsl-H10 body)
  `(FORALL nsp (FORALL c (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb
     (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) ,nsl-sp)
     (IMPLIES (IN s (IDS ,nsl-sp)) (IMPLIES (IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb)
     (IMPLIES (NOT (IN ((KINV ,nsl-sp) ,(nsl-ka 'pa)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (IN ((KINV ,nsl-sp) ,(nsl-ka 'pb)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (= na nb)) (IMPLIES (UNIQUELY-ORIGINATES ,nsl-sp nb) ,body)))))))))))))))))
(define (nsl-conds-510 z) (list (nsl-sub 'nb z) `(NOT ,(nsl-sub nsl-v0* z)) `(NOT ,(nsl-sub nsl-v3* z))))

;;; LEMMA 5.12: no minimal member of S = {n in C : Nb @ n, v0 not @ n, v3 not @ n} is an
;;; adversary node.  (The paper: "almost identical to the proof of Lemma 5.4 ... we must apply
;;; Proposition 3.3 to each of the two private keys": nsl-adversary-loss at K_A and at K_B.)
(sp (make-wff (nsl-H10 `(FORALL n2 ,(nsl-curry (nsl-min-conjs nsl-conds-510 'n2) `(NOT (IS-ADVERSARY-NODE ,nsl-isp n2)))))))
(dk-peel!)
(di)
(nsl-resp-setup! nsl-conds-510)
(let ((univ (nsl-min-univ nsl-conds-510 'n2)))
  (nsl-min-sent! nsl-conds-510 'n2 univ)
  (let* ((x (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c nsl-sp (nsl-S nsl-conds-510) 'nb '(LIST 2 s) 'n2))))
    (nsl-or-each! (nsl-min-or! (list (nsl-sub nsl-v0* x) (nsl-sub nsl-v3* x)) x univ)
      (lambda (d)
        (let* ((w (list-ref d 3))
               (z (dk-skolem! (dk-cite! 'nsl-adversary-loss 'nsp 'c 'n2 x (cadr w) (caddr w)))))
          (for-each (lambda (p) (dk-rewrite-h! p (nsl-c 'n2) (nsl-c z))) (nsl-conds-510 'n2))
          (ai (dk-apply! univ z)))))))
(qed 'nsl-lemma-5-12)

;;; LEMMA 5.11: no minimal member of S is a regular node.  The paper's cases, on the user's model:
;;; on a responder's strand t' (n2 = [2, t'] carries {N N' C}_KD): Nb = N puts [1, t'] in S; Nb = N'
;;; makes Nb originate at n2 (Lemma 5.3 for t'), against unique origination at [2, s], which is
;;; outside S; Nb = C is impossible, Nb not being a name -- A CASE THE PAPER OMITS ("either Nb = N or
;;; Nb = N'").  On an initiator's strand: at [1, t'] Nb would originate there (or be a name); at
;;; [3, t'] the second node {x Nb C}_K is in S unless it is v0, and then C = B, K_C = K_B and n2's
;;; content IS v3 (the paper: "C /= B, because otherwise v3 = term(m)").
(sp (make-wff (nsl-H10 `(FORALL n2 ,(nsl-curry (nsl-min-conjs nsl-conds-510 'n2) `(NOT (IS-REGULAR-NODE ,nsl-isp n2)))))))
(dk-peel!)
(di)
(nsl-resp-setup! nsl-conds-510)
(let ((univ (nsl-min-univ nsl-conds-510 'n2))
      (t2 '(NTH 2 n2)))
  (nsl-min-sent! nsl-conds-510 'n2 univ)
  (nsl-fact-split! 'node-parts nsl-sp 'n2)
  (nsl-project! 'is-regular-node `(IS-REGULAR-NODE ,nsl-isp n2) `(NOT (IN (NTH 2 n2) (ADV-IDS ,nsl-isp))))
  (nsl-strand-cases! t2
    (lambda (kind pa2 pb2 na2 nb2 lit)
      (nsl-lit3-sp! 'n2 'n2 lit
        (lambda (j)
          (if (or (and (eq? kind 'init) (= j 2)) (and (eq? kind 'resp) (not (= j 2))))
              (nsl-recv-absurd-sp! 'n2)
              (let ((cn (nsl-content-sp 'n2)))
                (nsl-fact-split! (if (eq? kind 'init) 'init-strand-nodes 'resp-strand-nodes) 'nsp t2 pa2 pb2 na2 nb2)
                (dk-rewrite-h! (nsl-sub 'nb 'n2) (nsl-c 'n2) cn)
                (let ((u0b (nsl-u0 pa2 pb2 na2)) (v0b (nsl-v0 pa2 pb2 na2 nb2))
                      ;; Nb at the first node of t': that node is in S
                      (first-in-S!
                        (lambda ()
                          (let ((n1 (nsl-before-in-bundle! 1 'n2 `(= (NTH 1 n2) ,j))))
                            (nsl-sub-node! 'nb n1 (nsl-u0 pa2 pb2 na2))
                            (nsl-not-sub-node! nsl-v0* n1 (nsl-u0 pa2 pb2 na2))
                            (nsl-not-sub-node! nsl-v3* n1 (nsl-u0 pa2 pb2 na2))
                            (ai (dk-apply! univ n1))))))
                  (nsl-or-each! (dk-subterm-literal! nsl-T nsl-K 'nb cn)
                    (lambda (e)
                      (let ((leaf (caddr e)))
                        (cond
                          ((equal? leaf pa2) (nsl-lit-neq-1! 'nb pa2))
                          ((equal? leaf pb2) (nsl-lit-neq-1! 'nb pb2))
                          ((and (eq? kind 'resp) (equal? leaf na2)) (first-in-S!))
                          ((eq? kind 'resp)                    ; Nb = N' on a responder's strand
                           (use-em `(= nb ,na2)
                             (lambda () (first-in-S!))
                             (lambda ()
                               (dk-have! `(NOT (= ,na2 ,nb2))
                                 (lambda ()
                                   (di)
                                   (dk-have! `(= nb ,na2) (lambda () (subst `(= nb ,nb2)) (nsl-subst-rfl! `(= ,nb2 ,na2))))
                                   (ai `(NOT (= nb ,na2)))))
                               (fact 'nsl-resp-nonce-originates 'nsp t2 pa2 pb2 na2 nb2)
                               (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,nb2 (LIST 2 ,t2)) nb2 'nb)
                               (nsl-orig-absurd! 'nb 'n2 2 '(LIST 2 s) nsl-conds-510))))
                          ((= j 1)                             ; Nb = Na' at an initiator's first node
                           (fact 'nsl-init-nonce-originates 'nsp t2 pa2 pb2 na2 nb2)
                           (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,na2 (LIST 1 ,t2)) na2 'nb)
                           (nsl-orig-absurd! 'nb 'n2 1 '(LIST 2 s) nsl-conds-510))
                          (#t                                  ; Nb = Nb' at an initiator's third node
                           (let ((n1 (nsl-before-in-bundle! 2 'n2 '(= (NTH 1 n2) 3))))
                             (nsl-sub-node! 'nb n1 v0b)
                             (nsl-not-sub-node! nsl-v3* n1 v0b)
                             (use-em (nsl-sub nsl-v0* n1)
                               (lambda ()
                                 (dk-rewrite-h! (nsl-sub nsl-v0* n1) (nsl-c n1) v0b)
                                 (nsl-flat-cases! nsl-v0* v0b
                                   (lambda ()
                                     ;; v0 is the second node's content: B' = B, so n2 carries v3
                                     (let ((l0 '(LIST na nb pb)) (l2 (cadr (cadr v0b))))
                                       (nsl-fact-split! 'encr-injective (cadr nsl-v0*) (caddr nsl-v0*) (cadr v0b) (caddr v0b))
                                       (dk-cite! 'lst-injective l0 l2)
                                       (dk-congr! `(= ,l0 ,l2) (lambda (t) `(NTH 3 ,t)) '==)
                                       (dk-nth-h! `(== (NTH 3 ,l0) (NTH 3 ,l2)))
                                       (dk-have! `(= pb ,pb2) (lambda () (nsl-subst-rfl! `(== pb ,pb2))))
                                       (fact 'subterm-refl nsl-T nsl-K nsl-v3*)
                                       (dk-have! (nsl-sub nsl-v3* 'n2)
                                         (lambda ()
                                           (subst `(== ,(nsl-c 'n2) ,cn))
                                           (subst `(= ,nb2 nb))
                                           (subst `(= ,pb2 pb))
                                           (dk-ass!)))
                                       (ai `(NOT ,(nsl-sub nsl-v3* 'n2)))))))
                               (lambda () (ai (dk-apply! univ n1))))))))))))))))))
(qed 'nsl-lemma-5-11)

;;; PROPOSITION 5.10 (secrecy of the responder's nonce): every node of C holding Nb holds v0 or v3.
(sp (make-wff (nsl-H10 `(FORALL m (IMPLIES (IN m (BNODES c)) (IMPLIES ,(nsl-sub 'nb 'm)
                          (OR ,(nsl-sub nsl-v0* 'm) ,(nsl-sub nsl-v3* 'm))))))))
(dk-peel!)
(use-em (nsl-sub nsl-v0* 'm)
  (lambda () (oi-l) (dk-ass!))
  (lambda ()
    (use-em (nsl-sub nsl-v3* 'm)
      (lambda () (oi-r) (dk-ass!))
      (lambda ()
        (nsl-nsl-space!)
        (let* ((r (nsl-minimal! nsl-conds-510 'm))
               (n2 (car r)))
          (use-em `(IS-ADVERSARY-NODE ,nsl-isp ,n2)
            (lambda () (ai (dk-cite! 'nsl-lemma-5-12 'nsp 'c 's 'pa 'pb 'na 'nb n2)))
            (lambda ()
              (dk-have! `(IS-REGULAR-NODE ,nsl-isp ,n2)
                (lambda ()
                  (mac 'is-regular-node)
                  (di)
                  (dk-have! `(IS-ADVERSARY-NODE ,nsl-isp ,n2) (lambda () (mac 'is-adversary-node) (dk-ass!)))
                  (ai `(NOT (IS-ADVERSARY-NODE ,nsl-isp ,n2)))))
              (ai (dk-cite! 'nsl-lemma-5-11 'nsp 'c 's 'pa 'pb 'na 'nb n2)))))))))
(qed 'nsl-responder-secrecy)

;;; "In particular, Nb /= term(m)": the nonce never travels in the clear.
(sp (make-wff (nsl-H10 `(FORALL m (IMPLIES (IN m (BNODES c)) (NOT (= ,(nsl-c 'm) nb)))))))
(dk-peel!)
(di)
(nsl-nsl-space!)
(nsl-open-strand! `(IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
(fact 'token-in-msgs nsl-T nsl-K 'nb)
(fact 'subterm-refl nsl-T nsl-K 'nb)
(dk-have! (nsl-sub 'nb 'm) (lambda () (nsl-subst-ass! `(= ,(nsl-c 'm) nb))))
(nsl-or-each! (dk-cite! 'nsl-responder-secrecy 'nsp 'c 's 'pa 'pb 'na 'nb 'm)
  (lambda (d)
    (let ((w (list-ref d 3)))
      (dk-rewrite-h! d (nsl-c 'm) 'nb)
      (fact 'subterm-of-token nsl-T nsl-K w 'nb)
      (nsl-token-eq-absurd! 'nb w))))
(qed 'nsl-responder-nonce-not-sent)

;;; -----------------------------------------------------------------------
;;; 13. THE INITIATOR'S GUARANTEES (section 5.5: Propositions 5.13, 5.14).
;;;
;;; PROPOSITION 5.13 AS THE PAPER STATES IT IS FALSE, twice:
;;;  (i) "for all m in C with Na @ term(m), {Na A}_KB @ term(m) or {Na Nb B}_KA @ term(m)" fails with
;;;      NO adversary at all: the initiator's first message is received by TWO responders (a sent
;;;      node may feed several received nodes of a bundle), the second of which answers
;;;      {Na Nb' B}_KA with its own Nb' /= Nb; that node holds Na and neither term.  The second
;;;      disjunct must range over the responder's value: {Na x B}_KA @ term(m) for SOME token x.
;;; (ii) with Na = Nb (allowed: only the responder's values are kept from names) the initiator's own
;;;      third node {Nb}_KB = {Na}_KB holds Na and neither term.  Hypothesis Na /= Nb added, as the
;;;      paper itself does for Propositions 5.2 and 5.10.
;;; Proposition 5.14 is proved from the corrected 5.13, so it carries Na /= Nb too.

;; (= LA LB) in context, LA LB literal lists of one length: land (= ai bi) at the indices IS
(define (nsl-list-eq-comps! la lb is)
  (for-each
    (lambda (i)
      (dk-congr! `(= ,la ,lb) (lambda (t) `(NTH ,i ,t)) '==)
      (let ((e (dk-nth-h! `(== (NTH ,i ,la) (NTH ,i ,lb)))))
        (if (not (dk-asm? `(= ,(cadr e) ,(caddr e))))
            (dk-have! `(= ,(cadr e) ,(caddr e)) (lambda () (nsl-subst-rfl! e))))))
    is))

;; (= EA EB) in context, EA EB encryptions of literal lists of one length: land the components
(define (nsl-encr-eq-comps! ea eb)
  (let ((la (cadr (cadr ea))) (lb (cadr (cadr eb))))
    (nsl-fact-split! 'encr-injective (cadr ea) (caddr ea) (cadr eb) (caddr eb))
    (dk-cite! 'lst-injective la lb)
    (nsl-list-eq-comps! la lb (iota (- (length la) 1) 1))))

(define nsl-u0* (nsl-u0 'pa 'pb 'na))
(define (nsl-wx x) (nsl-v0 'pa 'pb 'na x))
(define (nsl-H13 body)
  `(FORALL nsp (FORALL c (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb
     (IMPLIES (IS-NSL-SPACE nsp) (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) ,nsl-sp)
     (IMPLIES (IN s (IDS ,nsl-sp)) (IMPLIES (IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb)
     (IMPLIES (IN (LIST 3 s) (BNODES c))
     (IMPLIES (NOT (IN ((KINV ,nsl-sp) ,(nsl-ka 'pa)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (IN ((KINV ,nsl-sp) ,(nsl-ka 'pb)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (= na nb)) (IMPLIES (UNIQUELY-ORIGINATES ,nsl-sp na) ,body))))))))))))))))))
(define (nsl-no-wx z) `(FORALL nsw_ (IMPLIES (IN nsw_ ,nsl-T) (NOT ,(nsl-sub (nsl-wx 'nsw_) z)))))
(define (nsl-some-wx z) `(FORSOME nsw_ (AND (IN nsw_ ,nsl-T) ,(nsl-sub (nsl-wx 'nsw_) z))))
(define (nsl-conds-513 z) (list (nsl-sub 'na z) `(NOT ,(nsl-sub nsl-u0* z)) (nsl-no-wx z)))

;; the initiator's strand s: opened, its nodes, and [1, s] originating na outside S
(define (nsl-init-setup! conds-of)
  (nsl-nsl-space!)
  (nsl-open-strand! `(IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
  (nsl-fact-split! 'init-strand-nodes 'nsp 's 'pa 'pb 'na 'nb)
  (nsl-D-incl!)
  (fact 'nsl-init-nonce-originates 'nsp 's 'pa 'pb 'na 'nb)
  (fact 'subterm-refl nsl-T nsl-K nsl-u0*)
  (dk-have! (nsl-sub nsl-u0* '(LIST 1 s)) (lambda () (nsl-subst-ass! `(= ,(nsl-c '(LIST 1 s)) ,nsl-u0*))))
  (dk-have! `(NOT (IN (LIST 1 s) ,(nsl-S conds-of)))
    (lambda () (di) (nsl-open-S! conds-of '(LIST 1 s)) (ai `(NOT ,(nsl-sub nsl-u0* '(LIST 1 s)))))))

;; Y a bundle node preceding the minimal N2 (UNIV), Na @ content(Y): land the OR of u0 @ Y and
;; "some {Na x B}_KA @ Y", by minimality
(define (nsl-min-or-513! y univ)
  (let ((claim `(OR ,(nsl-sub nsl-u0* y) ,(nsl-some-wx y))))
    (dk-have! claim
      (lambda ()
        (use-em (nsl-sub nsl-u0* y)
          (lambda () (oi-l) (dk-ass!))
          (lambda ()
            (use-em (nsl-some-wx y)
              (lambda () (oi-r) (dk-ass!))
              (lambda ()
                (dk-have! (nsl-no-wx y)
                  (lambda ()
                    (let ((x (nsl-peel-var!)))
                      (di)
                      (dk-have! (nsl-some-wx y) (lambda () (ew x) (dk-conj-close! dk-ass!)))
                      (ai `(NOT ,(nsl-some-wx y))))))
                (ai (dk-apply! univ y))))))))
    claim))

;;; 5.13, the adversary case: no minimal member of S = {n in C : Na @ n, u0 not @ n, no {Na x B}_KA @ n}
;;; is an adversary node (nsl-adversary-loss at K_B for u0, at K_A for {Na x B}_KA).
(sp (make-wff (nsl-H13 `(FORALL n2 ,(nsl-curry (nsl-min-conjs nsl-conds-513 'n2) `(NOT (IS-ADVERSARY-NODE ,nsl-isp n2)))))))
(dk-peel!)
(di)
(nsl-init-setup! nsl-conds-513)
(let ((univ (nsl-min-univ nsl-conds-513 'n2)))
  (nsl-min-sent! nsl-conds-513 'n2 univ)
  (let ((y (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c nsl-sp (nsl-S nsl-conds-513) 'na '(LIST 1 s) 'n2))))
    (nsl-or-each! (nsl-min-or-513! y univ)
      (lambda (d)
        (let ((w (if (dk-head-is? d 'FORSOME)
                     (let ((x0 (dk-skolem! d)))
                       (dk-stl--msg! nsl-T nsl-K (nsl-wx x0))
                       (dk-apply! (nsl-no-wx 'n2) x0)
                       (nsl-wx x0))
                     nsl-u0*)))
          (let ((z (dk-skolem! (dk-cite! 'nsl-adversary-loss 'nsp 'c 'n2 y (cadr w) (caddr w)))))
            (for-each (lambda (p) (dk-rewrite-h! p (nsl-c 'n2) (nsl-c z))) (nsl-conds-513 'n2))
            (ai (dk-apply! univ z))))))))
(qed 'nsl-initiator-secrecy-adversary)

;;; 5.13, the regular case: no minimal member of S is a regular node.  On an initiator's strand t':
;;; at [1, t'] Na would originate there (or be a name); at [3, t'] ({Nb'}_KB' with Na = Nb') the
;;; second node {Na' Nb' B'}_KA' precedes n2 and holds Na, so by minimality it holds u0 (impossible:
;;; a pair is not a triple) or {Na x B}_KA, whence Na' = Na, t' = s by unique origination, Nb' = Nb,
;;; and Na = Nb -- refuted.  On a responder's strand (n2 = [2, t'] carries {Na' Nb' B'}_KA'): Na = Na'
;;; makes [1, t'] = {Na' A'}_KB' hold u0 by minimality, so A' = A, B' = B and n2 holds {Na Nb' B}_KA,
;;; against n2 in S; Na = Nb' (/= Na') makes Na originate at n2; Na = B' is a name.
(sp (make-wff (nsl-H13 `(FORALL n2 ,(nsl-curry (nsl-min-conjs nsl-conds-513 'n2) `(NOT (IS-REGULAR-NODE ,nsl-isp n2)))))))
(dk-peel!)
(di)
(nsl-init-setup! nsl-conds-513)
(let ((univ (nsl-min-univ nsl-conds-513 'n2))
      (t2 '(NTH 2 n2)))
  (nsl-min-sent! nsl-conds-513 'n2 univ)
  (nsl-fact-split! 'node-parts nsl-sp 'n2)
  (nsl-project! 'is-regular-node `(IS-REGULAR-NODE ,nsl-isp n2) `(NOT (IN (NTH 2 n2) (ADV-IDS ,nsl-isp))))
  (nsl-strand-cases! t2
    (lambda (kind pa2 pb2 na2 nb2 lit)
      (nsl-lit3-sp! 'n2 'n2 lit
        (lambda (j)
          (if (or (and (eq? kind 'init) (= j 2)) (and (eq? kind 'resp) (not (= j 2))))
              (nsl-recv-absurd-sp! 'n2)
              (let ((cn (nsl-content-sp 'n2))
                    (u0b (nsl-u0 pa2 pb2 na2)) (v0b (nsl-v0 pa2 pb2 na2 nb2)) (v3b (nsl-v3 pb2 nb2)))
                (nsl-fact-split! (if (eq? kind 'init) 'init-strand-nodes 'resp-strand-nodes) 'nsp t2 pa2 pb2 na2 nb2)
                (dk-rewrite-h! (nsl-sub 'na 'n2) (nsl-c 'n2) cn)
                (nsl-or-each! (dk-subterm-literal! nsl-T nsl-K 'na cn)
                  (lambda (e)
                    (let ((leaf (caddr e)))
                      (cond
                        ((equal? leaf pa2) (nsl-lit-neq-1! 'na pa2))
                        ((equal? leaf pb2) (nsl-lit-neq-1! 'na pb2))
                        ((and (eq? kind 'init) (= j 1))      ; Na = Na' at an initiator's first node
                         (fact 'nsl-init-nonce-originates 'nsp t2 pa2 pb2 na2 nb2)
                         (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,na2 (LIST 1 ,t2)) na2 'na)
                         (nsl-orig-absurd! 'na 'n2 1 '(LIST 1 s) nsl-conds-513))
                        ((eq? kind 'init)                    ; Na = Nb' at an initiator's third node
                         (let ((n1 (nsl-before-in-bundle! 2 'n2 '(= (NTH 1 n2) 3))))
                           (nsl-sub-node! 'na n1 v0b)
                           (nsl-or-each! (nsl-min-or-513! n1 univ)
                             (lambda (d)
                               (if (dk-head-is? d 'FORSOME)
                                   (let ((x0 (dk-skolem! d)))
                                     (dk-rewrite-h! (nsl-sub (nsl-wx x0) n1) (nsl-c n1) v0b)
                                     (nsl-flat-cases! (nsl-wx x0) v0b
                                       (lambda ()
                                         ;; Na' = Na: t' = s by unique origination, so Nb' = Nb, and Na = Nb
                                         (nsl-encr-eq-comps! (nsl-wx x0) v0b)
                                         (fact 'nsl-init-nonce-originates 'nsp t2 pa2 pb2 na2 nb2)
                                         (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,na2 (LIST 1 ,t2)) na2 'na)
                                         (fact 'originates-unique nsl-sp 'na '(LIST 1 s) `(LIST 1 ,t2))
                                         (nsl-fact-split! 'node-pair-injective 1 t2 1 's)
                                         (dk-rewrite-h! '(= n2 (LIST (NTH 1 n2) (NTH 2 n2))) '(NTH 1 n2) 3)
                                         (dk-rewrite-h! '(= n2 (LIST 3 (NTH 2 n2))) '(NTH 2 n2) 's)
                                         (dk-rewrite-h! `(== ,(nsl-c 'n2) ,cn) 'n2 '(LIST 3 s))
                                         (nsl-eq-via! v3b nsl-v3* (nsl-c '(LIST 3 s)))
                                         (nsl-fact-split! 'encr-injective nb2 (caddr v3b) 'nb (caddr nsl-v3*))
                                         (dk-have! '(= na nb) (lambda () (subst `(= na ,nb2)) (nsl-subst-rfl! `(= ,nb2 nb))))
                                         (ai '(NOT (= na nb))))))
                                   (begin
                                     (dk-rewrite-h! (nsl-sub nsl-u0* n1) (nsl-c n1) v0b)
                                     (nsl-flat-cases! nsl-u0* v0b (lambda () (nsl-lit-neq-1! nsl-u0* v0b)))))))))
                        (#t                                  ; a responder's second node
                         (let ((case-na2!
                                 (lambda ()
                                   (let ((n1 (nsl-before-in-bundle! 1 'n2 '(= (NTH 1 n2) 2))))
                                     (nsl-sub-node! 'na n1 u0b)
                                     (nsl-or-each! (nsl-min-or-513! n1 univ)
                                       (lambda (d)
                                         (if (dk-head-is? d 'FORSOME)
                                             (let ((x0 (dk-skolem! d)))
                                               (dk-rewrite-h! (nsl-sub (nsl-wx x0) n1) (nsl-c n1) u0b)
                                               (nsl-flat-cases! (nsl-wx x0) u0b (lambda () (nsl-lit-neq-1! (nsl-wx x0) u0b))))
                                             (begin
                                               (dk-rewrite-h! (nsl-sub nsl-u0* n1) (nsl-c n1) u0b)
                                               (nsl-flat-cases! nsl-u0* u0b
                                                 (lambda ()
                                                   ;; A' = A and B' = B: n2 holds {Na Nb' B}_KA
                                                   (nsl-encr-eq-comps! nsl-u0* u0b)
                                                   (dk-apply! nsl-pubkey-inj 'pb pb2)
                                                   (dk-stl--msg! nsl-T nsl-K (nsl-wx nb2))
                                                   (fact 'subterm-refl nsl-T nsl-K (nsl-wx nb2))
                                                   (dk-have! (nsl-sub (nsl-wx nb2) 'n2)
                                                     (lambda ()
                                                       (subst `(== ,(nsl-c 'n2) ,cn))
                                                       (subst `(= ,na2 na))
                                                       (subst `(= ,pa2 pa))
                                                       (subst `(= ,pb2 pb))
                                                       (dk-ass!)))
                                                   (ai (dk-apply! (nsl-no-wx 'n2) nb2))))))))))))
                           (if (equal? leaf na2)
                               (case-na2!)
                               (use-em `(= na ,na2)
                                 (lambda () (case-na2!))
                                 (lambda ()                  ; Na = Nb' /= Na': Na originates at n2
                                   (dk-have! `(NOT (= ,na2 ,nb2))
                                     (lambda ()
                                       (di)
                                       (dk-have! `(= na ,na2) (lambda () (subst `(= na ,nb2)) (nsl-subst-rfl! `(= ,nb2 ,na2))))
                                       (ai `(NOT (= na ,na2)))))
                                   (fact 'nsl-resp-nonce-originates 'nsp t2 pa2 pb2 na2 nb2)
                                   (dk-rewrite-h! `(ORIGINATES ,nsl-sp ,nb2 (LIST 2 ,t2)) nb2 'na)
                                   (nsl-orig-absurd! 'na 'n2 2 '(LIST 1 s) nsl-conds-513)))))))))))))))))
(qed 'nsl-initiator-secrecy-regular)

;;; PROPOSITION 5.13, CORRECTED (secrecy of the initiator's nonce): every node of C holding Na holds
;;; {Na A}_KB or {Na x B}_KA for some token x.
(sp (make-wff (nsl-H13 `(FORALL m (IMPLIES (IN m (BNODES c)) (IMPLIES ,(nsl-sub 'na 'm)
                          (OR ,(nsl-sub nsl-u0* 'm) ,(nsl-some-wx 'm))))))))
(dk-peel!)
(use-em (nsl-sub nsl-u0* 'm)
  (lambda () (oi-l) (dk-ass!))
  (lambda ()
    (use-em (nsl-some-wx 'm)
      (lambda () (oi-r) (dk-ass!))
      (lambda ()
        (dk-have! (nsl-no-wx 'm)
          (lambda ()
            (let ((x (nsl-peel-var!)))
              (di)
              (dk-have! (nsl-some-wx 'm) (lambda () (ew x) (dk-conj-close! dk-ass!)))
              (ai `(NOT ,(nsl-some-wx 'm))))))
        (nsl-nsl-space!)
        (let* ((r (nsl-minimal! nsl-conds-513 'm))
               (n2 (car r)))
          (use-em `(IS-ADVERSARY-NODE ,nsl-isp ,n2)
            (lambda () (ai (dk-cite! 'nsl-initiator-secrecy-adversary 'nsp 'c 's 'pa 'pb 'na 'nb n2)))
            (lambda ()
              (dk-have! `(IS-REGULAR-NODE ,nsl-isp ,n2)
                (lambda ()
                  (mac 'is-regular-node)
                  (di)
                  (dk-have! `(IS-ADVERSARY-NODE ,nsl-isp ,n2) (lambda () (mac 'is-adversary-node) (dk-ass!)))
                  (ai `(NOT (IS-ADVERSARY-NODE ,nsl-isp ,n2)))))
              (ai (dk-cite! 'nsl-initiator-secrecy-regular 'nsp 'c 's 'pa 'pb 'na 'nb n2)))))))))
(qed 'nsl-initiator-secrecy)

;;; "In particular, Na /= term(m)".
(sp (make-wff (nsl-H13 `(FORALL m (IMPLIES (IN m (BNODES c)) (NOT (= ,(nsl-c 'm) na)))))))
(dk-peel!)
(di)
(nsl-nsl-space!)
(nsl-open-strand! `(IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
(fact 'token-in-msgs nsl-T nsl-K 'na)
(fact 'subterm-refl nsl-T nsl-K 'na)
(dk-have! (nsl-sub 'na 'm) (lambda () (nsl-subst-ass! `(= ,(nsl-c 'm) na))))
(nsl-or-each! (dk-cite! 'nsl-initiator-secrecy 'nsp 'c 's 'pa 'pb 'na 'nb 'm)
  (lambda (d)
    (let ((w (if (dk-head-is? d 'FORSOME)
                 (let ((x0 (dk-skolem! d))) (dk-stl--msg! nsl-T nsl-K (nsl-wx x0)) (nsl-wx x0))
                 nsl-u0*)))
      (dk-rewrite-h! (nsl-sub w 'm) (nsl-c 'm) 'na)
      (fact 'subterm-of-token nsl-T nsl-K w 'na)
      (nsl-token-eq-absurd! 'na w))))
(qed 'nsl-initiator-nonce-not-sent)

;;; PROPOSITION 5.14 (the initiator's agreement): C contains a responder's strand t in
;;; Resp[A, B, Na, Nb] with C-height 2.  The paper's sketch: the minimal member m0 of
;;; {m in C : v0 @ term(m)} is regular -- then its strand is the responder's -- or an E node
;;; (encrypting Na Nb B under K_A), whose received plaintext holds Na in the clear inside a list
;;; of tokens, against the (corrected) Proposition 5.13.
(define (nsl-conds-514 z) (list (nsl-sub nsl-v0* z)))
(sp (make-wff (nsl-H13 `(FORSOME t (AND (IN t (IDS ,nsl-sp)) (AND (IS-RESP-STRAND nsp ((STRAND-MAP ,nsl-sp) t) pa pb na nb)
                                                                 (IN (LIST 2 t) (BNODES c))))))))
(dk-peel!)
(nsl-nsl-space!)
(nsl-open-strand! `(IS-INIT-STRAND nsp ((STRAND-MAP ,nsl-sp) s) pa pb na nb))
(nsl-fact-split! 'init-strand-nodes 'nsp 's 'pa 'pb 'na 'nb)
(nsl-D-incl!)
(fact 'bundle-space 'c)
;; [2, s] is in C (C-height 3) and holds v0
(dk-have! `(SAME-STRAND-BEFORE (BSPACE c) (LIST 2 s) (LIST 3 s))
  (lambda ()
    (subst `(= (BSPACE c) ,nsl-sp))
    (mac 'same-strand-before)
    (nth-r)
    (dk-conj-close! (lambda () (cond ((dk-ass!) #t) ((dk-head-is? (dk-goal) '=) (rfl)) (#t (dk-nn!)))))))
(dk-apply! (dk-cite! 'bundle-ssb-closed 'c '(LIST 3 s)) '(LIST 2 s))
(fact 'subterm-refl nsl-T nsl-K nsl-v0*)
(dk-have! (nsl-sub nsl-v0* '(LIST 2 s)) (lambda () (nsl-subst-ass! `(= ,(nsl-c '(LIST 2 s)) ,nsl-v0*))))
(let* ((r (nsl-minimal! nsl-conds-514 '(LIST 2 s)))
       (m0 (car r)) (univ (cdr r))
       (t2 `(NTH 2 ,m0)))
  (nsl-fact-split! 'node-parts nsl-sp m0)
  (use-em `(IS-ADVERSARY-NODE ,nsl-isp ,m0)
    ;; an adversary node: it received v0 earlier, or built it
    (lambda ()
      (nsl-or-each! (dk-cite! 'adversary-sent-source nsl-isp m0 nsl-v0*)
        (lambda (d)
          (if (dk-head-is? d 'FORSOME)
              (let ((x (dk-skolem! d)))
                (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,x ,m0) (lambda () (nsl-subst-ass! `(= (BSPACE c) ,nsl-sp))))
                (dk-apply! (dk-cite! 'bundle-ssb-closed 'c m0) x)
                (fact 'bundle-ssb-precedes 'c x m0)
                (nsl-ai-close! (dk-apply! univ x)))
              (begin
                (dk-split-all!)
                (nsl-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'ADV-TOKENS))) "the built cases")
                  (lambda (e)
                    (cond
                      ((dk-head-is? e 'IN)                     ; M: v0 is not a token
                       (dk-apply! (nsl-project! 'is-infiltrated-space `(IS-INFILTRATED-SPACE ,nsl-isp)
                                    `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS ,nsl-isp)) (IN sat_ ,nsl-T))))
                                  nsl-v0*)
                       (nsl-set! (cadr nsl-v0*)) (nsl-set! (caddr nsl-v0*))
                       (nsl-ai-close! (dk-cite! 'token-not-encr nsl-T (cadr nsl-v0*) (caddr nsl-v0*))))
                      ((dk-contains? e 'LST)                   ; C: v0 is not a list
                       (let ((l (dk-skolem! e)))
                         (nsl-eq-via! nsl-v0* `(LST ,l) (nsl-c m0))
                         (nsl-ai-close! (dk-cite! 'encr-ne-list (cadr nsl-v0*) (caddr nsl-v0*) l))))
                      (#t                                      ; E: the plaintext Na Nb B was received in the clear
                       (let* ((h (dk-skolem! e))
                              (k (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f h))) "the key")))
                              (x (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f 'SAME-STRAND-BEFORE))) "the plaintext node")))
                              (lp '(LST (LIST na nb pb))))
                         (nsl-eq-via! nsl-v0* `(ENCR ,h ,k) (nsl-c m0))
                         (nsl-fact-split! 'encr-injective lp (caddr nsl-v0*) h k)
                         (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,x ,m0) (lambda () (nsl-subst-ass! `(= (BSPACE c) ,nsl-sp))))
                         (dk-apply! (dk-cite! 'bundle-ssb-closed 'c m0) x)
                         (nsl-sub-fwd! 'na lp)
                         (dk-have! (nsl-sub 'na x)
                           (lambda () (subst `(= ,(nsl-c x) ,h)) (nsl-subst-ass! `(= ,h ,lp))))
                         (nsl-tuples-D! '(LIST na nb pb))
                         (nsl-or-each! (dk-cite! 'nsl-initiator-secrecy 'nsp 'c 's 'pa 'pb 'na 'nb x)
                           (lambda (f)
                             (let ((w (if (dk-head-is? f 'FORSOME)
                                          (let ((x0 (dk-skolem! f))) (dk-stl--msg! nsl-T nsl-K (nsl-wx x0)) (nsl-wx x0))
                                          nsl-u0*)))
                               (dk-have! `(IS-SUBTERM ,nsl-T ,nsl-K ,w ,lp)
                                 (lambda () (subst `(= ,lp ,h)) (nsl-subst-ass! `(= ,h ,(nsl-c x)))))
                               (nsl-or-each! (dk-cite! 'subterm-of-flat-list nsl-T nsl-K nsl-D w '(LIST na nb pb))
                                 (lambda (g)
                                   (if (dk-head-is? g '=)
                                       (nsl-ai-close! (dk-cite! 'encr-ne-list (cadr w) (caddr w) '(LIST na nb pb)))
                                       (nsl-D-absurd! w)))))))))))))))))
    ;; a regular node: its content is v0, so it is the second node of a responder's strand for A, B, Na, Nb
    (lambda ()
      (dk-have! `(IS-REGULAR-NODE ,nsl-isp ,m0)
        (lambda ()
          (mac 'is-regular-node)
          (di)
          (dk-have! `(IS-ADVERSARY-NODE ,nsl-isp ,m0) (lambda () (mac 'is-adversary-node) (dk-ass!)))
          (ai `(NOT (IS-ADVERSARY-NODE ,nsl-isp ,m0)))))
      (fact 'nsl-regular-encr-subterm 'nsp m0 (cadr nsl-v0*) (caddr nsl-v0*))
      (nsl-project! 'is-regular-node `(IS-REGULAR-NODE ,nsl-isp ,m0) `(NOT (IN ,t2 (ADV-IDS ,nsl-isp))))
      (nsl-strand-cases! t2
        (lambda (kind pa2 pb2 na2 nb2 lit)
          (nsl-lit3-sp! m0 m0 lit
            (lambda (j)
              (if (or (and (eq? kind 'init) (= j 2)) (and (eq? kind 'resp) (not (= j 2))))
                  (nsl-recv-absurd-sp! m0)
                  (let ((cn (nsl-content-sp m0)))
                    (nsl-eq-via! nsl-v0* cn (nsl-c m0))
                    (if (eq? kind 'init)
                        (nsl-lit-neq-1! nsl-v0* cn)
                        (begin
                          (nsl-encr-eq-comps! nsl-v0* cn)
                          (dk-apply! nsl-pubkey-inj 'pa pa2)
                          (let* ((h0 `(IS-RESP-STRAND nsp ,(nsl-sgs m0) ,pa2 ,pb2 ,na2 ,nb2))
                                 (h1 (dk-rewrite-h! h0 pa2 'pa))
                                 (h2 (dk-rewrite-h! h1 pb2 'pb))
                                 (h3 (dk-rewrite-h! h2 na2 'na))
                                 (h4 (dk-rewrite-h! h3 nb2 'nb)))
                            (dk-rewrite-h! `(= ,m0 (LIST (NTH 1 ,m0) (NTH 2 ,m0))) `(NTH 1 ,m0) 2)
                            (dk-have! `(IN (LIST 2 ,t2) (BNODES c)) (lambda () (nsl-subst-ass! `(= (LIST 2 ,t2) ,m0))))
                            (ew t2)
                            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "prop 5.14: open" (dk-goal)))))))))))))))))
(qed 'nsl-initiator-agreement)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing))
          '(pk-space-parts three-strand-node three-strand-nodes token-not-encr token-not-lst
            subterm-of-flat-list subterm-of-flat-encr-list subterm-of-flat-encr-token bundle-send-content))
(for-each (lambda (n) (topic! n 'constructions))
          '(init-strand-is-strand resp-strand-is-strand init-strand-nodes resp-strand-nodes
            nsl-regular-content nsl-regular-encr-subterm nsl-regular-list-subterm nsl-regular-no-key
            adversary-encr-loss adversary-sent-source bundle-minimal-sent-back bundle-minimal-earlier
            nsl-key-secret nsl-list-source nsl-adversary-loss nsl-resp-nonce-originates nsl-init-nonce-originates
            nsl-init-unique nsl-lemma-5-4 nsl-lemma-5-6 nsl-lemma-5-7 nsl-responder-agreement nsl-lemma-5-11
            nsl-lemma-5-12 nsl-responder-secrecy nsl-responder-nonce-not-sent nsl-initiator-secrecy-adversary
            nsl-initiator-secrecy-regular nsl-initiator-secrecy nsl-initiator-nonce-not-sent nsl-initiator-agreement))
