;;; nso-laws.scm -- THE ORIGINAL NEEDHAM-SCHROEDER PROTOCOL: Lemma 5.9 of Thayer, Herzog, Guttman
;;; (~/docs/jcs_strand_spaces.pdf, section 5.3): "In the original Needham-Schroeder protocol, a node n1 precedes
;;; n2 on the same regular strand t, and term(n1) = {Na Nb}_KA."  Version 2 (agent SB-2, 2026-10-26): the
;;; theorems are INSTANCES of theorem-library/flat-regular-laws.scm.  The protocol's own content is the
;;; flatness of its regular nodes (nso-regular-content, the NSL proof run on the NSO traces) and the two
;;; literal facts of Lemma 5.3 (nb is the 2nd component of {Na Nb}, nb is not in {Na A}); everything else is
;;; one citation.  Vocabulary: structure-library/nso.scm (SB-1).  Destination: theorem-library/nso-laws.scm
;;; (replaces SB-1's 1385-line copy).  Library strand.  Load window: after structure-library/nso and
;;; theorem-library/flat-regular-laws.  Helper prefix nso-; the helpers are copies of nsl.scm's.

;;; -----------------------------------------------------------------------
;;; helpers (prefix nsl-)

(define nso-sp '(ISPACE (PK-INF nsp)))
(define nso-T '(TOKENS (ISPACE (PK-INF nsp))))
(define nso-K '(KEYS (ISPACE (PK-INF nsp))))
(define nso-msgs '(MSG-SET (TOKENS (ISPACE (PK-INF nsp))) (KEYS (ISPACE (PK-INF nsp)))))

(define (nso-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(nso-and (cdr fs)))))
(define (nso-have-and! . fs)
  (let ((c (nso-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
    c))

;; land CLAIM, a projection of the predicate hypothesis HYP, on a lane (HYP survives)
(define (nso-project! pred hyp claim)
  (dk-have! claim
    (lambda ()
      (mac-h pred hyp)
      (if (not (dk-ass!))
          (begin
            (dk-split-all!)
            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-project!: not a projection" claim))))))))
  claim)

;; fact THM at ARGS unless its instance is already in context; split what landed
(define (nso-fact-split! thm . args)
  (let ((f (apply dk-cite! thm args)))
    (if (and (pair? f) (eq? (car f) 'AND)) (dk-split-all!))
    f))

;; the index X with (IN X NN), (<= 1 X), (<= X N) in context (N a numeral): run (BODY j) with
;; (= X j) in context, for each j = 1 .. N
(define (nso-index-cases! x n body)
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
(define (nso-select! j n)
  (cond ((= n 1) #t)
        ((= j 1) (oi-l))
        (#t (oi-r) (nso-select! (- j 1) (- n 1)))))


;; the parts of the public-key space nsp and of its strand space, landed and split
(define (nso-space!)
  (if (not (dk-asm? '(IS-STRAND-SPACE (ISPACE (PK-INF nsp)))))
      (begin
        (fact 'pk-space-parts 'nsp)
        (dk-split-all!)
        (fact 'strand-space-parts nso-sp)
        (dk-split-all!))))

;;; 2. THE REGULAR STRANDS: their traces are strands, their three nodes and contents.

(define (nso-ka x) `((PUBKEY nsp) ,x))
(define (nso-u0 pa pb na) `(ENCR (LST (LIST ,na ,pa)) ,(nso-ka pb)))
(define (nso-v0 pa pb na nb) `(ENCR (LST (LIST ,na ,nb)) ,(nso-ka pa)))
(define (nso-v3 pb nb) `(ENCR ,nb ,(nso-ka pb)))
(define (nso-dirs kind) (if (eq? kind 'init) '(SENT RECEIVED SENT) '(RECEIVED SENT RECEIVED)))
(define (nso-trace kind pa pb na nb)
  (let ((ds (nso-dirs kind)))
    `(LIST (LIST ,(car ds) ,(nso-u0 pa pb na))
           (LIST ,(cadr ds) ,(nso-v0 pa pb na nb))
           (LIST ,(caddr ds) ,(nso-v3 pb nb)))))
(define (nso-strand-pred kind) (if (eq? kind 'init) 'IS-NSO-INIT-STRAND 'IS-NSO-RESP-STRAND))
;; the conjuncts of IS-INIT-STRAND / IS-RESP-STRAND (structure-library/nsl.scm), in order
(define (nso-strand-conjs kind s pa pb na nb)
  (list `(IN ,pa (NAMES nsp)) `(IN ,pb (NAMES nsp)) `(IN ,na ,nso-T) `(IN ,nb ,nso-T)
        (if (eq? kind 'init) `(NOT (IN ,na (NAMES nsp))) `(NOT (IN ,nb (NAMES nsp))))
        `(NOT (IN ,na ,nso-K)) `(NOT (IN ,nb ,nso-K))
        `(= ,s ,(nso-trace kind pa pb na nb))))

(define nso-names-tokens '(FORALL x (IMPLIES (IN x (NAMES nsp)) (IN x (TOKENS (ISPACE (PK-INF nsp)))))))
(define nso-names-nonkeys '(FORALL x (IMPLIES (IN x (NAMES nsp)) (NOT (IN x (KEYS (ISPACE (PK-INF nsp))))))))
(define nso-pubkey-inj '(FORALL x (FORALL y (IMPLIES (IN x (NAMES nsp)) (IMPLIES (IN y (NAMES nsp))
                          (IMPLIES (= ((PUBKEY nsp) x) ((PUBKEY nsp) y)) (= x y)))))))

;; a name X (IN X (NAMES nsp)) in context: land X in T, X not in K, PUBKEY(X) in K
(define (nso-name! x)
  (if (not (dk-asm? `(IN ,x ,nso-T))) (dk-apply! nso-names-tokens x))
  (if (not (dk-asm? `(NOT (IN ,x ,nso-K)))) (dk-apply! nso-names-nonkeys x))
  (if (not (dk-asm? `(IN ,(nso-ka x) ,nso-K))) (fact 'fun-apply-type-c '(PUBKEY nsp) '(NAMES nsp) nso-K x)))

;; HYP = (IS-INIT-STRAND nsp S pa pb na nb) or the responder's, in context (IS-PK-SPACE nsp and
;; the space's parts too): land its conjuncts, the typings of the names, keys and the three
;; messages; return the trace literal
(define (nso-open-strand! hyp)
  (let* ((kind (if (eq? (car hyp) 'IS-NSO-INIT-STRAND) 'init 'resp))
         (args (cddr hyp))
         (s (car args)) (pa (cadr args)) (pb (caddr args)) (na (cadddr args)) (nb (car (cddddr args)))
         (conjs (nso-strand-conjs kind s pa pb na nb)))
    (if (not (dk-asm? (car (last-pair conjs))))
        (begin
          (dk-have! (nso-and conjs) (lambda () (mac-h (if (eq? kind 'init) 'IS-NSO-INIT-STRAND 'IS-NSO-RESP-STRAND) hyp) (dk-ass!)))
          (dk-split-all!)))
    (nso-name! pa)
    (nso-name! pb)
    (dk-stl--msg! nso-T nso-K (nso-u0 pa pb na))
    (dk-stl--msg! nso-T nso-K (nso-v0 pa pb na nb))
    (dk-stl--msg! nso-T nso-K (nso-v3 pb nb))
    (nso-trace kind pa pb na nb)))

;; (IN (LIST dir m) (DIRECTED T K)) for m typed in MSG-SET
(define (nso-directed! dir m)
  (fact 'directed-intro nso-T nso-K m)
  (dk-split-all!)
  `(IN (LIST ,dir ,m) (DIRECTED ,nso-T ,nso-K)))

;; with (= (NTH ... ) ...) / (== ...) facts about node contents and directions in context, all
;; NTH-reduced: close a goal (= (NODE-CONTENT sp n) m), (IS-SENT sp n), (IS-RECEIVED sp n), (IN ..)
(define (nso-eq-for lhs)
  (find-first (lambda (f) (and (pair? f) (memq (car f) '(= ==)) (equal? (cadr f) lhs) (equal? (reduce-nth-in-expr (caddr f)) (caddr f))))
              (dk-asms)))
(define (nso-node-closer!)
  (let ((g (dk-goal)))
    (cond ((dk-ass!) #t)
          ((memq (car g) '(IS-SENT IS-RECEIVED))
           (mac (if (eq? (car g) 'IS-SENT) 'is-sent 'is-received))
           (let ((e (nso-eq-for (cadr (dk-goal)))))
             (if (not e) (error "nsl-node-closer!: no direction equation" (dk-goal)))
             (nso-subst-rfl! e)))
          ((eq? (car g) '=)
           (let ((e (nso-eq-for (cadr g))))
             (if (not e) (error "nsl-node-closer!: no content equation" g))
             (nso-subst-rfl! e)))
          (#t (error "nsl-node-closer!: cannot close" g)))))

;; subst E on the focus goal, then rfl when what is left is (= x x)
(define (nso-subst-rfl! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (let ((g (dk-goal)))
          (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
              (rfl)
              (error "nsl-subst-rfl!: not reflexive after the rewrite" g))))))

;; reduce every NTH of a literal inside the context's == / = facts
(define (nso-nth-all!)
  (for-each (lambda (f) (if (and (pair? f) (memq (car f) '(= ==)) (dk-contains? f 'NTH)) (dk-nth-h! f)))
            (dk-asms)))

;; an OR in context, split to its leaves (right-nested); HANDLER gets the disjunct of each leaf
(define (nso-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (nso-or-each! (caddr o) handler))
            (#t (handler (caddr o))))))))

;; subst E on the focus goal, then `ass' when the leaf is still open
(define (nso-subst-ass! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (if (not (dk-ass!)) (error "nsl-subst-ass!: the rewritten goal is not in context" (dk-goal))))))


;;; is an encryption, under a key, of a non-key token or of a list of non-key tokens.

(define nso-D `(SEP nsd_ ,nso-T (NOT (IN nsd_ ,nso-K))))     ; the tokens that are not keys

(define nso-law
  `(FORALL nli_ (IMPLIES (IN nli_ (IDS ,nso-sp))
     (OR (IN nli_ (ADV-IDS (PK-INF nsp)))
         (OR (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
               (IS-NSO-INIT-STRAND nsp ((STRAND-MAP ,nso-sp) nli_) nla_ nlb_ nlm_ nln_)))))
             (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
               (IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) nli_) nla_ nlb_ nlm_ nln_))))))))))

;; IS-NSL-SPACE nsp in context: land IS-PK-SPACE, the space's parts and the strand law
(define (nso-nsl-space!)
  (nso-project! 'IS-NSO-SPACE '(IS-NSO-SPACE nsp) '(IS-PK-SPACE nsp))
  (nso-space!)
  (if (not (dk-asm? nso-law)) (nso-project! 'IS-NSO-SPACE '(IS-NSO-SPACE nsp) nso-law))
  nso-law)

;; the identifier ID (in IDS) is not an adversary's: the strand at ID is an initiator's or a
;; responder's.  NOTADV is (NOT (IN ID (ADV-IDS (PK-INF nsp)))) in context.  HANDLER gets

(define (nso-c n) `(NODE-CONTENT ,nso-sp ,n))
(define (nso-sub a n) `(IS-SUBTERM ,nso-T ,nso-K ,a ,(nso-c n)))
(define (nso-S conds-of) `(SEP nsz_ (BNODES c) ,(nso-and (conds-of 'nsz_))))
(define (nso-min-univ conds-of n2)
  `(FORALL z (IMPLIES (IN z (BNODES c))
     ,(fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) `(NOT (IN (LIST z ,n2) (PRECEDES-STRICT c))) (conds-of 'z)))))
(define (nso-min-conjs conds-of n2)
  (append (list `(IN ,n2 (BNODES c))) (conds-of n2) (list (nso-min-univ conds-of n2))))


(define nso-isp '(PK-INF nsp))

(define nso-v0* (nso-v0 'pa 'pb 'na 'nb))
(define nso-v3* (nso-v3 'pb 'nb))
(define (nso-H-resp body)
  `(FORALL nsp (FORALL c (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb
     (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IS-BUNDLE c) (IMPLIES (= (BSPACE c) ,nso-sp)
     (IMPLIES (IN s (IDS ,nso-sp)) (IMPLIES (IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) s) pa pb na nb)
     (IMPLIES (IN (LIST 3 s) (BNODES c))
     (IMPLIES (NOT (IN ((KINV ,nso-sp) ,(nso-ka 'pa)) (ADV-TOKENS (PK-INF nsp))))
     (IMPLIES (NOT (= na nb)) (IMPLIES (UNIQUELY-ORIGINATES ,nso-sp nb) ,body)))))))))))))))))
(define (nso-conds-54 z) (list (nso-sub 'nb z) `(NOT ,(nso-sub nso-v0* z))))
(define (nso-curry fs body) (fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) body fs))

;; (kind pa pb na nb lit) on each branch, the strand opened (nsl-open-strand!).
(define (nso-strand-cases! id handler)
  (let ((o (dk-apply! (nso-nsl-space!) id)))
    (nso-or-each! o
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
                   (hyp (dk-pick (lambda (f) (and (memq (car f) '(IS-NSO-INIT-STRAND IS-NSO-RESP-STRAND)) (dk-contains? f nb) (dk-contains? f id)))
                                 "the strand"))
                   (kind (if (eq? (car hyp) 'IS-NSO-INIT-STRAND) 'init 'resp))
                   (lit (nso-open-strand! hyp)))
              (handler kind pa pb na nb lit)))))))

;; the regular node N (in NODES sp, IS-REGULAR-NODE in context): HANDLER gets
;; (kind j pa pb na nb) for each of the six cases, with (= (NTH 1 N) j), and the content and
;; direction of N as reduced == facts, in context
(define (nso-regular-cases! n handler)
  (nso-nsl-space!)
  (nso-project! 'is-regular-node `(IS-REGULAR-NODE (PK-INF nsp) ,n) `(NOT (IN (NTH 2 ,n) (ADV-IDS (PK-INF nsp)))))
  (nso-fact-split! 'node-parts nso-sp n)
  (nso-strand-cases! `(NTH 2 ,n)
    (lambda (kind pa pb na nb lit)
      (let ((o (dk-cite! 'three-strand-node nso-sp n (cadr lit) (caddr lit) (cadddr lit))))
        (nso-or-each! o
          (lambda (d)
            (let ((j (caddr (cadr d))))
              (dk-split-all!)
              (nso-nth-all!)
              (handler kind j pa pb na nb))))))))

;; (IN X D) for X typed in T and not a key
(define (nso-in-D! x)
  (dk-have! `(IN ,x ,nso-D) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-ass!))))))

(sp (make-wff `(FORALL nsp (FORALL n (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IN n (NODES ,nso-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n)
    (FORSOME k (AND (IN k ,nso-K)
      (OR (FORSOME x (AND (IN x ,nso-D) (= (NODE-CONTENT ,nso-sp n) (ENCR x k))))
          (FORSOME l (AND (IN l (TUPLES ,nso-D)) (= (NODE-CONTENT ,nso-sp n) (ENCR (LST l) k))))))))))))))
(dk-peel!)
(nso-regular-cases! 'n
  (lambda (kind j pa pb na nb)
    (let* ((msg (case j ((1) (nso-u0 pa pb na)) ((2) (nso-v0 pa pb na nb)) (else (nso-v3 pb nb))))
           (key (caddr msg))
           (body (cadr msg)))
      (ew key)
      (dk-conj-close!
        (lambda ()
          (if (not (dk-ass!))
              (if (= j 3)
                  (begin
                    (nso-in-D! nb)
                    (oi-l) (ew nb)
                    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nso-subst-rfl! (nso-eq-for (cadr (dk-goal))))))))
                  (let ((l (cadr body)))
                    (for-each nso-in-D! (cdr l))
                    (dk-have! `(IN ,l (TUPLES ,nso-D)) (lambda () (dk-each-leaf! (lambda () (ti)) (lambda () (dk-ass!)))))
                    (oi-r) (ew l)
                    (dk-conj-close! (lambda () (if (not (dk-ass!)) (nso-subst-rfl! (nso-eq-for (cadr (dk-goal)))))))))))))))
(qed 'nso-regular-content)

;;; -----------------------------------------------------------------------
;;; THE INSTANCES.

;; the literal facts the general responder lemmas take as hypotheses: l0 a list of messages, nb a
;; subterm of LST(l0) (its 2nd component), nb not a subterm of u0 (Na /= Nb, Nb not a name)
(define (nso-flat-facts!)
  (let* ((v0 (nso-v0 'pa 'pb 'na 'nb)) (l0 (cadr (cadr v0))) (u0 (nso-u0 'pa 'pb 'na)))
    (dk-stl--tuples! nso-T nso-K l0)
    (dk-cite! 'token-in-msgs nso-T nso-K 'nb)
    (dk-cite! 'subterm-refl nso-T nso-K 'nb)
    (dk-have! `(IS-SUBTERM ,nso-T ,nso-K nb (NTH 2 ,l0)) (lambda () (nth-r) (dk-ass!)))
    (dk-have! '(IN 2 NN) (lambda () (arith)))
    (dk-have! '(<= 1 2) (lambda () (dk-nn!)))
    (dk-have! `(<= 2 (LENGTH ,l0)) (lambda () (len-r) (arith)))
    (dk-cite! 'subterm-component nso-T nso-K 'nb l0 2)
    (dk-have! `(NOT (IS-SUBTERM ,nso-T ,nso-K nb ,u0))
      (lambda ()
        (di)
        (nso-or-each! (dk-subterm-literal! nso-T nso-K 'nb u0)
          (lambda (e)
            (let ((a (caddr e)))
              (if (equal? a 'na)
                  (begin (dk-have! '(= na nb) (lambda () (subst '(= nb na)) (rfl)))
                         (ai '(NOT (= na nb))))
                  (begin (dk-have! '(IN nb (NAMES nsp)) (lambda () (subst `(= nb ,a)) (dk-ass!)))
                         (ai '(NOT (IN nb (NAMES nsp)))))))))))
    (list u0 l0 (nso-ka 'pa) (nso-ka 'pb))))

(sp (make-wff '(FORALL nsp (IMPLIES (IS-NSO-SPACE nsp) (IS-FLAT-REGULAR nsp)))))
(dk-peel!)
(mac 'is-flat-regular)
(dk-conj-close!
  (lambda ()
    (if (dk-head-is? (dk-goal) 'IS-PK-SPACE)
        (nso-project! 'is-nso-space '(IS-NSO-SPACE nsp) '(IS-PK-SPACE nsp))
        (let* ((landed (dk-peel!))
               (n (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-contains? f 'NODES))) landed))))
          (dk-cite! 'nso-regular-content 'nsp n)
          (dk-ass!)))))
(qed 'nso-flat)

(sp (make-wff `(FORALL nsp (FORALL n (FORALL g (FORALL y (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IN n (NODES ,nso-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN g ,nso-msgs) (IMPLIES (IN y ,nso-K)
  (IMPLIES (IS-SUBTERM ,nso-T ,nso-K (ENCR g y) (NODE-CONTENT ,nso-sp n))
    (= (ENCR g y) (NODE-CONTENT ,nso-sp n))))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-regular-encr-subterm 'nsp 'n 'g 'y)
(dk-ass!)
(qed 'nso-regular-encr-subterm)

(sp (make-wff `(FORALL nsp (FORALL n (FORALL m (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IN n (NODES ,nso-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN m (TUPLES ,nso-msgs))
  (IMPLIES (IS-SUBTERM ,nso-T ,nso-K (LST m) (NODE-CONTENT ,nso-sp n))
    (IN m (TUPLES ,nso-T))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-regular-list-subterm 'nsp 'n 'm)
(dk-ass!)
(qed 'nso-regular-list-subterm)

(sp (make-wff `(FORALL nsp (FORALL n (FORALL y (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IN n (NODES ,nso-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN y ,nso-K)
    (NOT (IS-SUBTERM ,nso-T ,nso-K y (NODE-CONTENT ,nso-sp n))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-regular-no-key 'nsp 'n 'y)
(dk-ass!)
(qed 'nso-regular-no-key)

(sp (make-wff `(FORALL nsp (FORALL c (FORALL y (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nso-sp) (IMPLIES (IN y ,nso-K) (IMPLIES (NOT (IN y (ADV-TOKENS (PK-INF nsp))))
    (FORALL n (IMPLIES (IN n (BNODES c)) (NOT (IS-SUBTERM ,nso-T ,nso-K y (NODE-CONTENT ,nso-sp n)))))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-key-secret 'nsp 'c 'y 'n)
(dk-ass!)
(qed 'nso-key-secret)

(sp (make-wff `(FORALL nsp (FORALL c (FORALL n2 (FORALL l (FORALL q (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nso-sp) (IMPLIES (IN n2 (BNODES c)) (IMPLIES (IN l (TUPLES ,nso-msgs))
  (IMPLIES (IN q NN) (IMPLIES (<= 1 q) (IMPLIES (<= q (LENGTH l))
  (IMPLIES (= (NODE-CONTENT ,nso-sp n2) (NTH q l))
  (IMPLIES (NOT (IN l (TUPLES ,nso-T)))
  (IMPLIES (FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x n2) (PRECEDES-STRICT c)) (IS-SUBTERM ,nso-T ,nso-K (LST l) (NODE-CONTENT ,nso-sp x)))))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z n2) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,nso-sp z) (NODE-CONTENT ,nso-sp n2)))))))))))))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-list-source 'nsp 'c 'n2 'l 'q)
(dk-ass!)
(qed 'nso-list-source)

(sp (make-wff `(FORALL nsp (FORALL c (FORALL m (FORALL x (FORALL g (FORALL y (IMPLIES (IS-NSO-SPACE nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,nso-sp) (IMPLIES (IN m (BNODES c)) (IMPLIES (IS-ADVERSARY-NODE (PK-INF nsp) m)
  (IMPLIES (IS-SENT ,nso-sp m) (IMPLIES (SAME-STRAND-BEFORE ,nso-sp x m)
  (IMPLIES (IN g ,nso-msgs) (IMPLIES (IN y ,nso-K) (IMPLIES (NOT (IN ((KINV ,nso-sp) y) (ADV-TOKENS (PK-INF nsp))))
  (IMPLIES (IS-SUBTERM ,nso-T ,nso-K (ENCR g y) (NODE-CONTENT ,nso-sp x))
  (IMPLIES (NOT (IS-SUBTERM ,nso-T ,nso-K (ENCR g y) (NODE-CONTENT ,nso-sp m)))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z m) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,nso-sp z) (NODE-CONTENT ,nso-sp m)))))))))))))))))))))))))
(dk-peel!)
(fact 'nso-flat 'nsp)
(dk-cite! 'flat-adversary-loss 'nsp 'c 'm 'x 'g 'y)
(dk-ass!)
(qed 'nso-adversary-loss)

;;; LEMMA 5.3: an instance of flat-resp-nonce-originates.
(sp (make-wff `(FORALL nsp (FORALL s (FORALL pa (FORALL pb (FORALL na (FORALL nb (IMPLIES (IS-PK-SPACE nsp)
  (IMPLIES (IN s (IDS ,nso-sp)) (IMPLIES (IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) s) pa pb na nb)
  (IMPLIES (NOT (= na nb)) (ORIGINATES ,nso-sp nb (LIST 2 s))))))))))))))
(dk-peel!)
(nso-space!)
(nso-open-strand! `(IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) s) pa pb na nb))
(let ((xs (nso-flat-facts!)))
  (dk-cite! 'flat-resp-nonce-originates 'nsp 's (car xs) (cadr xs) (caddr xs) (cadddr xs) 'nb)
  (dk-ass!))
(qed 'nso-resp-nonce-originates)

;;; LEMMA 5-4: an instance of flat-lemma-5-4.
(sp (make-wff (nso-H-resp
  `(FORSOME n2 ,(nso-and (append (nso-min-conjs nso-conds-54 'n2)
                                 (list `(IS-REGULAR-NODE ,nso-isp n2) `(IS-SENT ,nso-sp n2))))))))
(dk-peel!)
(nso-nsl-space!)
(fact 'nso-flat 'nsp)
(nso-open-strand! `(IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) s) pa pb na nb))
(let ((xs (nso-flat-facts!)))
  (dk-cite! 'flat-lemma-5-4 'nsp 'c 's (car xs) (cadr xs) (caddr xs) (cadddr xs) 'nb)
  (dk-ass!))
(qed 'nso-lemma-5-4)

;;; LEMMA 5-6: an instance of flat-lemma-5-6.
(sp (make-wff (nso-H-resp
  `(FORALL n2 ,(nso-curry (append (nso-min-conjs nso-conds-54 'n2) (list `(IS-REGULAR-NODE ,nso-isp n2) `(IS-SENT ,nso-sp n2)))
     `(FORSOME n1 (AND (SAME-STRAND-BEFORE ,nso-sp n1 n2) (= ,(nso-c 'n1) ,nso-v0*))))))))
(dk-peel!)
(nso-nsl-space!)
(fact 'nso-flat 'nsp)
(nso-open-strand! `(IS-NSO-RESP-STRAND nsp ((STRAND-MAP ,nso-sp) s) pa pb na nb))
(let ((xs (nso-flat-facts!)))
  (dk-cite! 'flat-lemma-5-6 'nsp 'c 's (car xs) (cadr xs) (caddr xs) (cadddr xs) 'nb 'n2)
  (dk-ass!))
(qed 'nso-lemma-5-9)
