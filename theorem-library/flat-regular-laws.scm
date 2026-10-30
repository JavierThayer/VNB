;;; flat-regular-laws.scm -- THE NSL ARGUMENT, ONCE, OVER ANY PUBLIC-KEY SPACE WHOSE REGULAR CONTENTS ARE
;;; FLAT (IS-FLAT-REGULAR, structure-library/flat-regular.scm).  Thayer, Herzog, Guttman,
;;; ~/docs/jcs_strand_spaces.pdf, section 5: the lemmas behind Lemmas 5.3, 5.4, 5.6 (and, for the original
;;; protocol, 5.9), stated for a responder strand with an arbitrary trace
;;;     <-u0, +{l0}_ka, -{nb}_kb>     (u0 any message, l0 any list of messages)
;;; and the two facts the paper's 5.3 uses: nb a subterm of the list l0, and nb not a subterm of u0.
;;; Agent SB-2, wave MAP-1026, 2026-10-26.  Destination: theorem-library/flat-regular-laws.scm.
;;; Library: strand.  Helper prefix frl-.
;;;
;;; ORIGIN.  The drivers are those of theorem-library/nsl.scm (agent S-3, 2026-10-07), sections 4, 7, 8,
;;; 10, 11, copied token-aware (nsl- -> frl-); the only changes: (1) IS-NSL-SPACE is replaced by
;;; IS-FLAT-REGULAR, and the flatness of the regular contents -- nsl-regular-content, the one place the
;;; NSL traces were used -- is now the definition (flat-regular-content projects it); (2) Lemma 5.3 is
;;; stated over the responder's trace with the two subterm facts as hypotheses (flat-resp-nonce-originates),
;;; and the trace's three nodes are read off any literal three-entry trace (resp-trace-nodes); (3) in
;;; Lemma 5.4 the disequation v0 /= v3 is shown for a list variable l0 (frl-v0-v3-absurd!) where nsl.scm
;;; compared two literals.  Instances: theorem-library/nsl-from-flat.scm (NSL) and theorem-library/nso-laws.scm
;;; (the original protocol).
;;;
;;; LOAD WINDOW: after structure-library/flat-regular and theorem-library/nsl, whose general lemmas are
;;; cited (three-strand-node(s), subterm-of-flat-encr-token / -list, adversary-encr-loss,
;;; adversary-sent-source, bundle-send-content, bundle-minimal-sent-back, bundle-minimal-earlier,
;;; pk-space-parts, token-not-encr / -lst).  If nsl.scm is later cut down to its instances, those general
;;; lemmas (its sections 1, 3, 5, 6) move to the head of this file.

;;; -----------------------------------------------------------------------
;;; helpers (prefix nsl-)

(define frl-sp '(ISPACE (PK-INF nsp)))
(define frl-T '(TOKENS (ISPACE (PK-INF nsp))))
(define frl-K '(KEYS (ISPACE (PK-INF nsp))))
(define frl-msgs '(MSG-SET (TOKENS (ISPACE (PK-INF nsp))) (KEYS (ISPACE (PK-INF nsp)))))

(define (frl-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(frl-and (cdr fs)))))
(define (frl-have-and! . fs)
  (let ((c (frl-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
    c))

;; land CLAIM, a projection of the predicate hypothesis HYP, on a lane (HYP survives)
(define (frl-project! pred hyp claim)
  (dk-have! claim
    (lambda ()
      (mac-h pred hyp)
      (if (not (dk-ass!))
          (begin
            (dk-split-all!)
            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-project!: not a projection" claim))))))))
  claim)

;; fact THM at ARGS unless its instance is already in context; split what landed
(define (frl-fact-split! thm . args)
  (let ((f (apply dk-cite! thm args)))
    (if (and (pair? f) (eq? (car f) 'AND)) (dk-split-all!))
    f))

;; the index X with (IN X NN), (<= 1 X), (<= X N) in context (N a numeral): run (BODY j) with
;; (= X j) in context, for each j = 1 .. N
(define (frl-index-cases! x n body)
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
(define (frl-select! j n)
  (cond ((= n 1) #t)
        ((= j 1) (oi-l))
        (#t (oi-r) (frl-select! (- j 1) (- n 1)))))


;; the parts of the public-key space nsp and of its strand space, landed and split
(define (frl-space!)
  (if (not (dk-asm? '(IS-STRAND-SPACE (ISPACE (PK-INF nsp)))))
      (begin
        (fact 'pk-space-parts 'nsp)
        (dk-split-all!)
        (fact 'strand-space-parts frl-sp)
        (dk-split-all!))))

;; with (= (NTH ... ) ...) / (== ...) facts about node contents and directions in context, all
;; NTH-reduced: close a goal (= (NODE-CONTENT sp n) m), (IS-SENT sp n), (IS-RECEIVED sp n), (IN ..)
(define (frl-eq-for lhs)
  (find-first (lambda (f) (and (pair? f) (memq (car f) '(= ==)) (equal? (cadr f) lhs) (equal? (reduce-nth-in-expr (caddr f)) (caddr f))))
              (dk-asms)))
(define (frl-node-closer!)
  (let ((g (dk-goal)))
    (cond ((dk-ass!) #t)
          ((memq (car g) '(IS-SENT IS-RECEIVED))
           (mac (if (eq? (car g) 'IS-SENT) 'is-sent 'is-received))
           (let ((e (frl-eq-for (cadr (dk-goal)))))
             (if (not e) (error "nsl-node-closer!: no direction equation" (dk-goal)))
             (frl-subst-rfl! e)))
          ((eq? (car g) '=)
           (let ((e (frl-eq-for (cadr g))))
             (if (not e) (error "nsl-node-closer!: no content equation" g))
             (frl-subst-rfl! e)))
          (#t (error "nsl-node-closer!: cannot close" g)))))

;; subst E on the focus goal, then rfl when what is left is (= x x)
(define (frl-subst-rfl! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (let ((g (dk-goal)))
          (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
              (rfl)
              (error "nsl-subst-rfl!: not reflexive after the rewrite" g))))))

;; reduce every NTH of a literal inside the context's == / = facts
(define (frl-nth-all!)
  (for-each (lambda (f) (if (and (pair? f) (memq (car f) '(= ==)) (dk-contains? f 'NTH)) (dk-nth-h! f)))
            (dk-asms)))

;; an OR in context, split to its leaves (right-nested); HANDLER gets the disjunct of each leaf
(define (frl-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (frl-or-each! (caddr o) handler))
            (#t (handler (caddr o))))))))

;; subst E on the focus goal, then `ass' when the leaf is still open
(define (frl-subst-ass! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (if (not (dk-ass!)) (error "nsl-subst-ass!: the rewritten goal is not in context" (dk-goal))))))


;;; is an encryption, under a key, of a non-key token or of a list of non-key tokens.

(define frl-D `(SEP nsd_ ,frl-T (NOT (IN nsd_ ,frl-K))))     ; the tokens that are not keys

;; IS-FLAT-REGULAR nsp in context: land IS-PK-SPACE and the parts of the space
(define (frl-nsl-space!)
  (frl-project! 'is-flat-regular '(IS-FLAT-REGULAR nsp) '(IS-PK-SPACE nsp))
  (frl-space!))

;;; THE FLATNESS, as the citable form nsl.scm proved for NSL (nsl-regular-content).
(sp (make-wff `(FORALL nsp (FORALL n (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IN n (NODES ,frl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n)
    (FORSOME k (AND (IN k ,frl-K)
      (OR (FORSOME x (AND (IN x ,frl-D) (= (NODE-CONTENT ,frl-sp n) (ENCR x k))))
          (FORSOME l (AND (IN l (TUPLES ,frl-D)) (= (NODE-CONTENT ,frl-sp n) (ENCR (LST l) k))))))))))))))
(dk-peel!)
(mac-h 'is-flat-regular '(IS-FLAT-REGULAR nsp))
(dk-split-all!)
(dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'IS-REGULAR-NODE))) "the flatness") 'n)
(dk-ass!)
(qed 'flat-regular-content)



;; (IN X D) for X typed in T and not a key
(define (frl-in-D! x)
  (dk-have! `(IN ,x ,frl-D) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-ass!))))))


;; (FORALL z (IMPLIES (IN z D) (IN z T))) for the non-key tokens D
(define frl-D-incl `(FORALL z (IMPLIES (IN z ,frl-D) (IN z ,frl-T))))
(define (frl-D-incl!)
  (dk-have! frl-D-incl
    (lambda ()
      (let ((z (cadr (car (dk-peel!)))))
        (sep-me `(IN ,z ,frl-D))
        (if (not (dk-ass!)) (error "nsl-D-incl!: open" (dk-goal))))))
  frl-D-incl)

;; the content of the regular node N, by nsl-regular-content: ON-TOKEN gets (k x) with
;; (= c (ENCR x k)), (IN x D), (IN k K) in context; ON-LIST gets (k l) with (IN l (TUPLES D))
(define (frl-rc-cases! n on-token on-list)
  (let* ((ex (dk-cite! 'flat-regular-content 'nsp n))
         (k (dk-skolem! ex))
         (o (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f k) (dk-contains? f 'NODE-CONTENT))) "the two shapes")))
    (frl-or-each! o
      (lambda (d)
        (if (dk-contains? d 'LST)
            (let ((l (dk-skolem! d))) (on-list k l))
            (let ((x (dk-skolem! d))) (on-token k x)))))))

;; `ai' a negation whose positive is in context: the focus leaf must close
(define (frl-ai-close! f)
  (let ((leaf (proof-state-focus *ps*)))
    (ai f)
    (if (not (sequent-node-grounded? leaf)) (error "nsl-ai-close!: the leaf is still open after ai" f))))

;; (IN W D) in context, W an encryption, a list message or a key (in K): absurd
(define (frl-D-absurd! w)
  (dk-landed* (lambda () (sep-me `(IN ,w ,frl-D))))
  (cond ((dk-head-is? w 'ENCR)
         (if (not (dk-asm? `(IN ,w ,frl-msgs))) (dk-stl--msg! frl-T frl-K w))
         (frl-set! (cadr w)) (frl-set! (caddr w))
         (frl-ai-close! (dk-cite! 'token-not-encr frl-T (cadr w) (caddr w))))
        ((dk-head-is? w 'LST)
         (frl-set! (cadr w))
         (frl-ai-close! (dk-cite! 'token-not-lst frl-T (cadr w))))
        (#t (frl-ai-close! `(NOT (IN ,w ,frl-K))))))

;; land (IN TERM SET) from a typing in context, through LST / ENCR
(define (frl-set! t)
  (let ((goal `(IN ,t SET)))
    (cond ((dk-asm? goal) goal)
          ((find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) t) (not (eq? (caddr f) 'SET)))) (dk-asms))
           => (lambda (ty) (fact 'membership-implies-sethood t (caddr ty)) goal))
          ((dk-head-is? t 'LST)
           (frl-set! (cadr t))
           (fact 'lst-in-tuples-set (cadr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          ((dk-head-is? t 'ENCR)
           (frl-set! (cadr t)) (frl-set! (caddr t))
           (fact 'encr-in-tuples-set (cadr t) (caddr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          (#t (error "nsl-set!: no typing for" t)))))

;; W in T (in context) and (= W TERM) in context (either orientation), TERM an encryption or a
;; list message: absurd (the token law; TERM may contain W, so no rewriting)
(define (frl-token-eq-absurd! w term)
  (if (not (dk-asm? `(= ,w ,term))) (dk-have! `(= ,w ,term) (lambda () (frl-subst-rfl! `(= ,term ,w)))))
  (cond ((dk-head-is? term 'ENCR)
         (frl-set! (cadr term)) (frl-set! (caddr term))
         (ai (dk-cite! 'encr-ne-token frl-T w (cadr term) (caddr term))))
        (#t
         (frl-set! (cadr term))
         (ai (dk-cite! 'token-ne-list frl-T w (cadr term))))))

;;; R1: an encryption inside a regular content IS the content (the paper, Lemma 5.6: "no regular
;;; node contains an encrypted term as a proper subterm").
(sp (make-wff `(FORALL nsp (FORALL n (FORALL g (FORALL y (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IN n (NODES ,frl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN g ,frl-msgs) (IMPLIES (IN y ,frl-K)
  (IMPLIES (IS-SUBTERM ,frl-T ,frl-K (ENCR g y) (NODE-CONTENT ,frl-sp n))
    (= (ENCR g y) (NODE-CONTENT ,frl-sp n))))))))))))))
(dk-peel!)
(frl-nsl-space!)
(frl-D-incl!)
(let* ((c `(NODE-CONTENT ,frl-sp n))
       (w '(ENCR g y))
       (hyp `(IS-SUBTERM ,frl-T ,frl-K ,w ,c)))
  (frl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-token frl-T frl-K frl-D w x k)
        (lambda (d)
          (if (dk-head-is? d '=) (frl-subst-ass! `(= ,c (ENCR ,x ,k))) (frl-D-absurd! w)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-list frl-T frl-K frl-D w l k)
        (lambda (d)
          (cond ((and (dk-head-is? d '=) (dk-head-is? (caddr d) 'ENCR)) (frl-subst-ass! `(= ,c (ENCR (LST ,l) ,k))))
                ((dk-head-is? d '=) (ai (dk-cite! 'encr-ne-list 'g 'y l)))
                (#t (frl-D-absurd! w))))))))
(qed 'flat-regular-encr-subterm)

;;; R2: a list message inside a regular content is a list of TOKENS (the paper, Lemma 5.4 case S:
;;; "no regular node contains a subterm g h where h contains any encrypted subterm").
(sp (make-wff `(FORALL nsp (FORALL n (FORALL m (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IN n (NODES ,frl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN m (TUPLES ,frl-msgs))
  (IMPLIES (IS-SUBTERM ,frl-T ,frl-K (LST m) (NODE-CONTENT ,frl-sp n))
    (IN m (TUPLES ,frl-T))))))))))))
(dk-peel!)
(frl-nsl-space!)
(frl-D-incl!)
(let* ((c `(NODE-CONTENT ,frl-sp n))
       (w '(LST m))
       (hyp `(IS-SUBTERM ,frl-T ,frl-K ,w ,c)))
  (frl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-token frl-T frl-K frl-D w x k)
        (lambda (d)
          (if (dk-head-is? d '=) (ai (dk-cite! 'lst-ne-encr 'm x k)) (frl-D-absurd! w)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-list frl-T frl-K frl-D w l k)
        (lambda (d)
          (cond ((and (dk-head-is? d '=) (dk-head-is? (caddr d) 'ENCR)) (ai (dk-cite! 'lst-ne-encr 'm `(LST ,l) k)))
                ((dk-head-is? d '=)
                 (dk-cite! 'lst-injective 'm l)
                 (dk-apply! (dk-cite! 'tuples-mono frl-D frl-T) l)
                 (frl-subst-ass! `(= m ,l)))
                (#t (frl-D-absurd! w))))))))
(qed 'flat-regular-list-subterm)

;;; R3: no key is a subterm of a regular content (the names and nonces are not keys, and the key
;;; of an encryption is not a subterm of it).
(sp (make-wff `(FORALL nsp (FORALL n (FORALL y (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IN n (NODES ,frl-sp))
  (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) n) (IMPLIES (IN y ,frl-K)
    (NOT (IS-SUBTERM ,frl-T ,frl-K y (NODE-CONTENT ,frl-sp n))))))))))))
(dk-peel!)
(di)
(frl-nsl-space!)
(frl-D-incl!)
(dk-apply! (dk-cite! 'keys-in-tokens frl-sp) 'y)
(let* ((c `(NODE-CONTENT ,frl-sp n))
       (hyp `(IS-SUBTERM ,frl-T ,frl-K y ,c)))
  (frl-rc-cases! 'n
    (lambda (k x)
      (dk-rewrite-h! hyp c `(ENCR ,x ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-token frl-T frl-K frl-D 'y x k)
        (lambda (d)
          (if (dk-head-is? d '=) (frl-token-eq-absurd! 'y (caddr d)) (frl-D-absurd! 'y)))))
    (lambda (k l)
      (dk-rewrite-h! hyp c `(ENCR (LST ,l) ,k))
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-list frl-T frl-K frl-D 'y l k)
        (lambda (d)
          (if (dk-head-is? d '=) (frl-token-eq-absurd! 'y (caddr d)) (frl-D-absurd! 'y)))))))
(qed 'flat-regular-no-key)


;; contradictory NN premises: close the focus goal
(define (frl-nn-absurd! . prems)
  (dk-have! '(< 0 0) (lambda () (apply dk-nn! prems)))
  (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
  (ai (dk-cite! 'rr-lt-irrefl 0)))


;;; 7. NSL: SECRET KEYS, AND THE ADVERSARY'S LOSSES.

;;; AN UNCOMPROMISED KEY NEVER APPEARS: a key y of an NSL space that the adversary does not know
;;; is a subterm of no node of any bundle.  The adversary bound (Prop. 3.3) at y; its hypothesis
;;; "y originates on no regular node" holds because no key is a subterm of a regular content
;;; (nsl-regular-no-key) -- the paper's "no initiator strand or responder strand originates K_A^-1"
;;; (Lemma 5.4, case D), which in this model is TRUE ONLY BECAUSE names and nonces are not keys.
(sp (make-wff `(FORALL nsp (FORALL c (FORALL y (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,frl-sp) (IMPLIES (IN y ,frl-K) (IMPLIES (NOT (IN y (ADV-TOKENS (PK-INF nsp))))
    (FORALL n (IMPLIES (IN n (BNODES c)) (NOT (IS-SUBTERM ,frl-T ,frl-K y (NODE-CONTENT ,frl-sp n)))))))))))))))
(let* ((landed (dk-peel!))
       (n (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BNODES c)))) landed))))
  (frl-nsl-space!)
  (dk-apply! (dk-cite! 'keys-in-tokens frl-sp) 'y)
  (dk-have! `(FORALL nr (IMPLIES (IN nr (BNODES c)) (IMPLIES (IS-REGULAR-NODE (PK-INF nsp) nr) (NOT (ORIGINATES ,frl-sp y nr)))))
    (lambda ()
      (let ((nr (cadr (find-first (lambda (f) (dk-head-is? f 'IN)) (dk-peel!)))))
        (di)
        (frl-fact-split! 'originates-elim frl-sp 'y nr)
        (ai (dk-cite! 'flat-regular-no-key 'nsp nr 'y)))))
  (dk-apply! (dk-cite! 'adversary-bound '(PK-INF nsp) 'c 'y) n)
  (dk-ass!))
(qed 'flat-key-secret)

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
(sp (make-wff `(FORALL nsp (FORALL c (FORALL n2 (FORALL l (FORALL q (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,frl-sp) (IMPLIES (IN n2 (BNODES c)) (IMPLIES (IN l (TUPLES ,frl-msgs))
  (IMPLIES (IN q NN) (IMPLIES (<= 1 q) (IMPLIES (<= q (LENGTH l))
  (IMPLIES (= (NODE-CONTENT ,frl-sp n2) (NTH q l))
  (IMPLIES (NOT (IN l (TUPLES ,frl-T)))
  (IMPLIES (FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x n2) (PRECEDES-STRICT c)) (IS-SUBTERM ,frl-T ,frl-K (LST l) (NODE-CONTENT ,frl-sp x)))))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z n2) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,frl-sp z) (NODE-CONTENT ,frl-sp n2)))))))))))))))))))))))
(let* ((landed (dk-peel!))
       (ex (find-first (lambda (f) (dk-head-is? f 'FORSOME)) landed))
       (sp0 frl-sp)
       (cond-of (lambda (v) `(AND (IN (LIST ,v n2) (PRECEDES-STRICT c)) (IS-SUBTERM ,frl-T ,frl-K (LST l) (NODE-CONTENT ,sp0 ,v)))))
       (tt `(SEP nst_ (BNODES c) ,(cond-of 'nst_)))
       (isp '(PK-INF nsp)))
  (frl-nsl-space!)
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
          (frl-fact-split! 'bundle-send-content 'c sp0 a b)
          (sep-me `(IN ,b ,tt))
          (dk-split-all!)
          (fact 'bundle-send-precedes 'c a b)
          (fact 'precedes-strict-trans 'c a b 'n2)
          (dk-rewrite-h! `(IS-SUBTERM ,frl-T ,frl-K (LST l) (NODE-CONTENT ,sp0 ,b)) `(NODE-CONTENT ,sp0 ,b) `(NODE-CONTENT ,sp0 ,a))
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
        (frl-or-each! (dk-cite! 'adversary-sent-source isp m0 '(LST l))
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
                  (frl-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'ADV-TOKENS))) "the built cases")
                    (lambda (e)
                      (cond
                        ((dk-head-is? e 'IN)               ; M: a known token is not a list
                         (dk-apply! (frl-project! 'is-infiltrated-space `(IS-INFILTRATED-SPACE ,isp)
                                      `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS ,isp)) (IN sat_ ,frl-T))))
                                    '(LST l))
                         (frl-set! 'l)
                         (ai (dk-cite! 'token-not-lst frl-T 'l)))
                        ((dk-contains? e 'LST)              ; C: LST(l) = LST(l2), n2's content was received earlier
                         (let* ((l2 (dk-skolem! e))
                                (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f l2))) "the components")))
                           (dk-have! `(= (LST l) (LST ,l2))
                             (lambda () (frl-subst-ass! `(= (LST l) (NODE-CONTENT ,sp0 ,m0)))))
                           (dk-cite! 'lst-injective 'l l2)
                           (dk-have! `(<= q (LENGTH ,l2)) (lambda () (frl-subst-ass! `(= ,l2 l))))
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
                                       (fact 'length-in-nn frl-msgs l2)
                                       (frl-have-and! '(IN q NN) `(IN ,l2 (TUPLES ,frl-msgs)) '(<= 1 q) `(<= q (LENGTH ,l2)))
                                       (fact 'nth-in-range frl-msgs 'q l2)
                                       (rfl))))))))
                        (#t                                 ; E: LST(l) is not an encryption
                         (let* ((h (dk-skolem! e))
                                (e2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f h))) "the key"))
                                (k (dk-skolem! e2)))
                           (dk-have! `(= (LST l) (ENCR ,h ,k))
                             (lambda () (frl-subst-ass! `(= (LST l) (NODE-CONTENT ,sp0 ,m0)))))
                           (ai (dk-cite! 'lst-ne-encr 'l h k))))))))))))
      ;; a regular node: LST(l) inside a regular content is a list of tokens
      (lambda ()
        (dk-have! `(IS-REGULAR-NODE ,isp ,m0)
          (lambda ()
            (mac 'is-regular-node)
            (di)
            (dk-have! `(IS-ADVERSARY-NODE ,isp ,m0) (lambda () (mac 'is-adversary-node) (dk-ass!)))
            (ai `(NOT (IS-ADVERSARY-NODE ,isp ,m0)))))
        (fact 'flat-regular-list-subterm 'nsp m0 'l)
        (ai `(NOT (IN l (TUPLES ,frl-T))))))))
(qed 'flat-list-source)

;;; AN ADVERSARY NODE CANNOT LOSE A SECRET ENCRYPTION.  m is a sent adversary node of a bundle of
;;; an NSL space, an earlier node x of its strand holds ENCR(g, y), m's content does not, and the
;;; adversary does not know KINV(y).  Then a bundle node z preceding m has m's content.  (The
;;; decryption D would need KINV(y) on a bundle node: nsl-key-secret; the separation S is the
;;; inner argument: nsl-list-source.)  This is the paper's case analysis of Lemma 5.4, once.
(sp (make-wff `(FORALL nsp (FORALL c (FORALL m (FORALL x (FORALL g (FORALL y (IMPLIES (IS-FLAT-REGULAR nsp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) ,frl-sp) (IMPLIES (IN m (BNODES c)) (IMPLIES (IS-ADVERSARY-NODE (PK-INF nsp) m)
  (IMPLIES (IS-SENT ,frl-sp m) (IMPLIES (SAME-STRAND-BEFORE ,frl-sp x m)
  (IMPLIES (IN g ,frl-msgs) (IMPLIES (IN y ,frl-K) (IMPLIES (NOT (IN ((KINV ,frl-sp) y) (ADV-TOKENS (PK-INF nsp))))
  (IMPLIES (IS-SUBTERM ,frl-T ,frl-K (ENCR g y) (NODE-CONTENT ,frl-sp x))
  (IMPLIES (NOT (IS-SUBTERM ,frl-T ,frl-K (ENCR g y) (NODE-CONTENT ,frl-sp m)))
    (FORSOME z (AND (IN z (BNODES c)) (AND (IN (LIST z m) (PRECEDES-STRICT c))
      (= (NODE-CONTENT ,frl-sp z) (NODE-CONTENT ,frl-sp m)))))))))))))))))))))))))
(dk-peel!)
(frl-nsl-space!)
(fact 'bundle-space 'c)
(dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) 'm)
(dk-rewrite-h! '(IN m (NODES (BSPACE c))) '(BSPACE c) frl-sp)
(fact 'adversary-encr-loss '(PK-INF nsp) 'm 'x 'g 'y)
(dk-split-all!)
(let* ((n1 '(LIST 1 (NTH 2 m)))
       (c1 `(NODE-CONTENT ,frl-sp ,n1)))
  (dk-have! `(SAME-STRAND-BEFORE (BSPACE c) ,n1 m) (lambda () (frl-subst-ass! `(= (BSPACE c) ,frl-sp))))
  (dk-apply! (dk-cite! 'bundle-ssb-closed 'c 'm) n1)
  (fact 'bundle-ssb-precedes 'c n1 'm)
  (frl-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'KINV))) "S or D")
    (lambda (d)
      (if (dk-head-is? d '=)
          ;; D: the strand's first node received KINV(y), which the adversary cannot have
          (let ((kv `((KINV ,frl-sp) y)))
            (fact 'kinv-in-fun frl-sp)
            (fact 'fun-apply-type-c `(KINV ,frl-sp) frl-K frl-K 'y)
            (dk-apply! (dk-cite! 'keys-in-tokens frl-sp) kv)
            (fact 'token-in-msgs frl-T frl-K kv)
            (fact 'subterm-refl frl-T frl-K kv)
            (dk-have! `(IS-SUBTERM ,frl-T ,frl-K ,kv ,c1) (lambda () (frl-subst-ass! `(= ,c1 ,kv))))
            (ai (dk-apply! (dk-cite! 'flat-key-secret 'nsp 'c kv) n1)))
          ;; S: the list l of the first node holds ENCR(g, y), so not every component is a token
          (let* ((l (dk-skolem! d))
                 (q (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f l))) "the index"))))
            (fact 'length-in-nn frl-msgs l)
            (dk-have! `(NOT (IN ,l (TUPLES ,frl-T)))
              (lambda ()
                (di)
                (frl-or-each! (dk-cite! 'subterm-of-list frl-T frl-K '(ENCR g y) l)
                  (lambda (e)
                    (if (dk-head-is? e '=)
                        (ai (dk-cite! 'encr-ne-list 'g 'y l))
                        (let ((j (dk-skolem! e)))
                          (frl-have-and! `(IN ,j NN) `(IN ,l (TUPLES ,frl-T)) `(<= 1 ,j) `(<= ,j (LENGTH ,l)))
                          (fact 'nth-in-range frl-T j l)
                          (fact 'subterm-of-token frl-T frl-K '(ENCR g y) `(NTH ,j ,l))
                          (frl-token-eq-absurd! `(NTH ,j ,l) '(ENCR g y))))))))
            (fact 'list-in-msgs frl-T frl-K l)
            (fact 'subterm-refl frl-T frl-K `(LST ,l))
            (dk-have! `(FORSOME x (AND (IN x (BNODES c)) (AND (IN (LIST x m) (PRECEDES-STRICT c))
                          (IS-SUBTERM ,frl-T ,frl-K (LST ,l) (NODE-CONTENT ,frl-sp x)))))
              (lambda ()
                (ew n1)
                (dk-conj-close! (lambda () (if (not (dk-ass!)) (frl-subst-ass! `(= ,c1 (LST ,l))))))))
            (fact 'flat-list-source 'nsp 'c 'm l q)
            (dk-ass!))))))
(qed 'flat-adversary-loss)

;;; 8. LITERAL MESSAGES: forward subterms, and disequalities.

;; does the token A occur in the literal M, as a leaf equal to A or equated to A in context?
(define (frl-leaf-match? a x)
  (or (equal? a x) (dk-asm? `(= ,a ,x)) (dk-asm? `(= ,x ,a))))
(define (frl-occurs? a m)
  (cond ((dk-stl--encr? m) (frl-occurs? a (cadr m)))
        ((dk-stl--lst? m) (any-pred (lambda (mi) (frl-occurs? a mi)) (cdr (cadr m))))
        (#t (frl-leaf-match? a m))))

;; land (IS-SUBTERM T K A M) for a literal M in which A occurs (leaves typed)
(define (frl-sub-fwd! a m)
  (let ((goal `(IS-SUBTERM ,frl-T ,frl-K ,a ,m)))
    (cond ((dk-asm? goal) goal)
          ((equal? a m)
           (dk-stl--msg! frl-T frl-K m)
           (fact 'subterm-refl frl-T frl-K m)
           goal)
          ((dk-stl--encr? m)
           (frl-sub-fwd! a (cadr m))
           (dk-stl--msg! frl-T frl-K (cadr m))
           (fact 'subterm-encr frl-T frl-K a (cadr m) (caddr m))
           goal)
          ((dk-stl--lst? m)
           (let* ((l (cadr m))
                  (ms (cdr l))
                  (i (let loop ((ms ms) (i 1))
                       (cond ((null? ms) (error "nsl-sub-fwd!: does not occur" a m))
                             ((frl-occurs? a (car ms)) i)
                             (#t (loop (cdr ms) (+ i 1))))))
                  (mi (list-ref ms (- i 1))))
             (frl-sub-fwd! a mi)
             (dk-stl--tuples! frl-T frl-K l)
             (dk-have! `(IS-SUBTERM ,frl-T ,frl-K ,a (NTH ,i ,l)) (lambda () (nth-r) (dk-ass!)))
             (dk-have! `(IN ,i NN) (lambda () (arith)))
             (dk-have! `(<= 1 ,i) (lambda () (dk-nn!)))
             (dk-have! `(<= ,i (LENGTH ,l)) (lambda () (len-r) (arith)))
             (fact 'subterm-component frl-T frl-K a l i)
             goal))
          ((frl-leaf-match? a m)                   ; a token leaf equated to A
           (dk-stl--msg! frl-T frl-K m)
           (fact 'subterm-refl frl-T frl-K m)
           (dk-have! goal (lambda () (frl-subst-ass! `(= ,a ,m))))
           goal)
          (#t (error "nsl-sub-fwd!: not a literal message" m)))))

;; two literal terms A, B: are they known to differ (shape, length, or a token disequation)?
(define (frl-distinct? a b)
  (cond ((and (dk-stl--encr? a) (dk-stl--encr? b)) (frl-distinct? (cadr a) (cadr b)))
        ((and (dk-stl--lst? a) (dk-stl--lst? b))
         (let ((as (cdr (cadr a))) (bs (cdr (cadr b))))
           (or (not (= (length as) (length bs)))
               (let loop ((as as) (bs bs)) (and (pair? as) (or (frl-distinct? (car as) (car bs)) (loop (cdr as) (cdr bs))))))))
        ((or (dk-stl--encr? a) (dk-stl--lst? a) (dk-stl--encr? b) (dk-stl--lst? b)) #t)
        (#t (or (dk-asm? `(NOT (= ,a ,b))) (dk-asm? `(NOT (= ,b ,a)))
                (and (dk-asm? `(IN ,a (NAMES nsp))) (dk-asm? `(NOT (IN ,b (NAMES nsp)))))
                (and (dk-asm? `(IN ,b (NAMES nsp))) (dk-asm? `(NOT (IN ,a (NAMES nsp)))))))))

;; (= A B) in context (either orientation, = or ==), A and B literal and nsl-distinct?: close the goal
(define (frl-lit-neq! a b)
  (cond
    ((dk-asm? `(= ,b ,a)) (if (dk-asm? `(= ,a ,b)) (frl-lit-neq-1! a b) (frl-lit-neq-1! b a)))
    ((dk-asm? `(= ,a ,b)) (frl-lit-neq-1! a b))
    ((or (dk-asm? `(== ,a ,b)) (dk-asm? `(== ,b ,a)))
     (dk-have! `(= ,a ,b) (lambda () (subst `(== ,a ,b)) (rfl)))
     (frl-lit-neq-1! a b))
    (#t (error "nsl-lit-neq!: no equation in context" a b))))

(define (frl-lit-neq-1! a b)               ; (= A B) in context
  (cond
    ((and (dk-stl--encr? a) (dk-stl--encr? b))
     (frl-fact-split! 'encr-injective (cadr a) (caddr a) (cadr b) (caddr b))
     (frl-lit-neq! (cadr a) (cadr b)))
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
               (frl-nn-absurd! `(= ,nb0 ,na0))))
           (let loop ((i 1) (as (cdr la)) (bs (cdr lb)))
             (cond ((null? as) (error "nsl-lit-neq!: the lists do not differ" la lb))
                   ((frl-distinct? (car as) (car bs))
                    (dk-congr! `(= ,la ,lb) (lambda (t) `(NTH ,i ,t)) '==)
                    (dk-nth-h! `(== (NTH ,i ,la) (NTH ,i ,lb)))
                    (frl-lit-neq! (car as) (car bs)))
                   (#t (loop (+ i 1) (cdr as) (cdr bs))))))))
    ((and (dk-stl--encr? a) (dk-stl--lst? b)) (ai (dk-cite! 'encr-ne-list (cadr a) (caddr a) (cadr b))))
    ((and (dk-stl--lst? a) (dk-stl--encr? b)) (ai (dk-cite! 'lst-ne-encr (cadr a) (cadr b) (caddr b))))
    ((or (dk-stl--encr? b) (dk-stl--lst? b)) (frl-token-eq-absurd! a b))
    ((or (dk-stl--encr? a) (dk-stl--lst? a))
     (dk-have! `(= ,b ,a) (lambda () (frl-subst-rfl! `(= ,a ,b))))
     (frl-token-eq-absurd! b a))
    ((dk-asm? `(NOT (= ,a ,b))) (ai `(NOT (= ,a ,b))))
    ((dk-asm? `(NOT (= ,b ,a)))
     (dk-have! `(= ,b ,a) (lambda () (frl-subst-rfl! `(= ,a ,b))))
     (ai `(NOT (= ,b ,a))))
    ((dk-asm? `(NOT (IN ,b (NAMES nsp))))
     (dk-rewrite-h! `(IN ,a (NAMES nsp)) a b)
     (ai `(NOT (IN ,b (NAMES nsp)))))
    ((dk-asm? `(NOT (IN ,a (NAMES nsp))))
     (dk-have! `(IN ,a (NAMES nsp)) (lambda () (frl-subst-ass! `(= ,a ,b))))
     (ai `(NOT (IN ,a (NAMES nsp)))))
    (#t (error "nsl-lit-neq!: cannot tell apart" a b))))


;;; 10. MINIMAL NODES OF CONTENT-DEFINED SETS.  A set S = {z in C : P(content(z))}, P a list of
;;; conjuncts CONDS-OF(z); "n2 is minimal in S" is written with the conjuncts curried:
;;;   n2 in C, P(n2), and forall z in C. P(z) => not z < n2.

(define (frl-c n) `(NODE-CONTENT ,frl-sp ,n))
(define (frl-sub a n) `(IS-SUBTERM ,frl-T ,frl-K ,a ,(frl-c n)))
(define (frl-S conds-of) `(SEP nsz_ (BNODES c) ,(frl-and (conds-of 'nsz_))))
(define (frl-min-univ conds-of n2)
  `(FORALL z (IMPLIES (IN z (BNODES c))
     ,(fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) `(NOT (IN (LIST z ,n2) (PRECEDES-STRICT c))) (conds-of 'z)))))
(define (frl-min-conjs conds-of n2)
  (append (list `(IN ,n2 (BNODES c))) (conds-of n2) (list (frl-min-univ conds-of n2))))

;; dk-peel!, returning the eigenvariable of the first guard (IN v _) that landed
(define (frl-peel-var!)
  (let ((landed (dk-peel!)))
    (cadr (or (find-first (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)) (equal? (caddr f) '(BNODES c)))) landed)
              (find-first (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)
              (error "nsl-peel-var!: no guard landed" landed)))))

;; (IN Z S) from Z in C and its conjuncts in context
(define (frl-in-S! conds-of z)
  (let ((ss (frl-S conds-of)))
    (dk-have! `(IN ,z ,ss) (lambda () (in-sep! (lambda () (dk-ass!)) (lambda () (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-in-S!: open" (dk-goal)))))))))))

;; open (IN Z S): land Z in C and its conjuncts
(define (frl-open-S! conds-of z)
  (let ((ss (frl-S conds-of)))
    (dk-have! (frl-and (cons `(IN ,z (BNODES c)) (conds-of z)))
      (lambda () (sep-me `(IN ,z ,ss)) (dk-split-all!) (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "nsl-open-S!: open" (dk-goal)))))))
    (dk-split-all!)))

;; the minimality of N2 in S in its SEP form, from the curried universal UNIV in context
(define (frl-minS! conds-of n2 univ)
  (let* ((ss (frl-S conds-of))
         (f `(FORALL z (IMPLIES (IN z ,ss) (NOT (IN (LIST z ,n2) (PRECEDES-STRICT c)))))))
    (dk-have! f
      (lambda ()
        (let ((z (cadr (car (dk-peel!)))))
          (frl-open-S! conds-of z)
          (dk-apply! univ z)
          (if (not (dk-ass!)) (error "nsl-minS!: open" (dk-goal))))))
    f))

;; N2 minimal in S (the curried universal UNIV and N2's conjuncts in context): N2 is SENT (Lemma 2.8,
;; S being closed under equal contents), and N2 is a node of the space
(define (frl-min-sent! conds-of n2 univ)
  (let ((ss (frl-S conds-of)))
    (fact 'bundle-space 'c)
    (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
      (lambda () (let ((z (cadr (car (dk-peel!))))) (frl-open-S! conds-of z) (dk-ass!))))
    (dk-have! `(FORALL x (FORALL y (IMPLIES (IN x (BNODES c)) (IMPLIES (IN y (BNODES c))
                 (IMPLIES (= (NODE-CONTENT (BSPACE c) x) (NODE-CONTENT (BSPACE c) y)) (IMPLIES (IN y ,ss) (IN x ,ss)))))))
      (lambda ()
        (dk-peel!)
        (let* ((eqn (find-first (lambda (f) (and (dk-head-is? f '=) (dk-head-is? (cadr f) 'NODE-CONTENT))) (dk-asms)))
               (x (caddr (cadr eqn))) (y (caddr (caddr eqn)))
               (eq2 (dk-rewrite-h! eqn '(BSPACE c) frl-sp)))
          (frl-open-S! conds-of y)
          (for-each (lambda (p) (dk-rewrite-h! p (frl-c y) (frl-c x))) (conds-of y))
          (frl-in-S! conds-of x))))
    (frl-in-S! conds-of n2)
    (frl-minS! conds-of n2 univ)
    (fact 'bundle-minimal-sent 'c ss n2)
    (dk-rewrite-h! `(IS-SENT (BSPACE c) ,n2) '(BSPACE c) frl-sp)
    (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) n2)
    (dk-rewrite-h! `(IN ,n2 (NODES (BSPACE c))) '(BSPACE c) frl-sp)))

;; the minimal member of S, given a member W: returns n2 with its conjuncts, the curried
;; minimality UNIV, IS-SENT, and n2 in NODES landed; returns (n2 . univ)
(define (frl-minimal! conds-of w)
  (let ((ss (frl-S conds-of)))
    (frl-in-S! conds-of w)
    (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
      (lambda () (let ((z (cadr (car (dk-peel!))))) (frl-open-S! conds-of z) (dk-ass!))))
    (dk-have! `(FORSOME w (IN w ,ss)) (lambda () (ew w) (dk-ass!)))
    (let* ((n2 (dk-skolem! (dk-cite! 'bundle-minimal 'c ss)))
           (minS (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f n2) (dk-contains? f 'PRECEDES-STRICT))) "n2 minimal"))
           (univ (frl-min-univ conds-of n2)))
      (frl-open-S! conds-of n2)
      (dk-have! univ
        (lambda ()
          (let ((z (frl-peel-var!)))
            (frl-in-S! conds-of z)
            (dk-apply! minS z)
            (if (not (dk-ass!)) (error "nsl-minimal!: open" (dk-goal))))))
      (frl-min-sent! conds-of n2 univ)
      (cons n2 univ))))

;; with N2 minimal (UNIV in context) and X a bundle node preceding N2 ((IN (LIST X N2) PS) in
;; context): X fails one of the conjuncts.  The conjuncts are (P1 (NOT P2)), P1 holds at X:
;; land CLAIM = P2 at X, by contradiction with the minimality
(define (frl-by-minimality! claim x univ)
  (dk-have! claim
    (lambda ()
      (use-em claim
        (lambda () (dk-ass!))
        (lambda ()
          (ai (dk-apply! univ x)))))))


;;; 11. AGREEMENT: THE RESPONDER'S GUARANTEE (section 5.2: Lemmas 5.3, 5.4, 5.6, 5.7, Prop. 5.2).

(define frl-isp '(PK-INF nsp))
(define (frl-sgs n) `((STRAND-MAP ,frl-sp) (NTH 2 ,n)))

;; the node N of a strand of sp whose trace is the literal LIT ((= sigma(NTH 2 N0) LIT) in context,
;; (= (NTH 2 N) (NTH 2 N0)) too when N /= N0): HANDLER gets the index j, N's content and direction
;; landed reduced
(define (frl-lit3-sp! n n0 lit handler)
  (if (not (equal? n n0))
      (dk-rewrite-h! `(= ,(frl-sgs n0) ,lit) `(NTH 2 ,n0) `(NTH 2 ,n)))
  (frl-or-each! (dk-cite! 'three-strand-node frl-sp n (cadr lit) (caddr lit) (cadddr lit))
    (lambda (d)
      (dk-split-all!)
      (frl-nth-all!)
      (handler (caddr (cadr d))))))

;; IS-SENT sp N and (== (NODE-DIR sp N) RECEIVED) in context: close the goal
(define (frl-recv-absurd-sp! n)
  (dk-have! `(= (NODE-DIR ,frl-sp ,n) SENT) (lambda () (mac-h 'is-sent `(IS-SENT ,frl-sp ,n)) (dk-ass!)))
  (dk-have! '(= SENT RECEIVED)
    (lambda () (subst `(= SENT (NODE-DIR ,frl-sp ,n))) (frl-subst-rfl! `(= (NODE-DIR ,frl-sp ,n) RECEIVED))))
  (ai (dk-cite! 'sent-ne-received)))

;; the strand order X ==> N opened (kept), with X's parts
(define (frl-ssb-open-sp! x n)
  (frl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,frl-sp ,x ,n)
    `(AND (IN ,x (NODES ,frl-sp)) (AND (IN ,n (NODES ,frl-sp)) (AND (= (NTH 2 ,x) (NTH 2 ,n)) (< (NTH 1 ,x) (NTH 1 ,n))))))
  (dk-split-all!)
  (frl-fact-split! 'node-parts frl-sp x))

;; X ==> N (opened) and N regular: X regular
(define (frl-regular-before! x n)
  (frl-project! 'is-regular-node `(IS-REGULAR-NODE ,frl-isp ,n) `(NOT (IN (NTH 2 ,n) (ADV-IDS ,frl-isp))))
  (dk-have! `(IS-REGULAR-NODE ,frl-isp ,x)
    (lambda () (mac 'is-regular-node) (frl-subst-ass! `(= (NTH 2 ,x) (NTH 2 ,n))))))

;; (= A B) from (= A C) or (= C A) and (== C B) / (= C B) in context, B certified
(define (frl-eq-via! a b cterm)
  (dk-have! `(= ,a ,b)
    (lambda ()
      (let ((leaf (proof-state-focus *ps*)))
        (subst `(= ,a ,cterm))
        (if (not (sequent-node-grounded? leaf))
            (if (not (dk-ass!))
                (frl-subst-rfl! (if (dk-asm? `(== ,cterm ,b)) `(== ,cterm ,b) `(== ,b ,cterm)))))))))

;; the statements of section 5.2: the hypotheses of Proposition 5.2

;;; -----------------------------------------------------------------------
;;; 11'. THE RESPONDER'S TRACE <-u0, +{l0}_ka, -{nb}_kb>, ANY u0 AND l0.

(define (frl-curry fs body) (fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) body fs))
(define (frl-foralls vs body) (fold-right (lambda (v acc) `(FORALL ,v ,acc)) body vs))
(define (frl-rtrace u0 v0 v3) `(LIST (LIST RECEIVED ,u0) (LIST SENT ,v0) (LIST RECEIVED ,v3)))
(define frl-v0* '(ENCR (LST l0) ka))
(define frl-v3* '(ENCR nb kb))

;;; The three nodes of a strand whose trace is <-u0, +v0, -v3>: memberships, directions, contents.
(sp (make-wff (frl-foralls '(nsp a u0 v0 v3)
  (frl-curry (list '(IS-PK-SPACE nsp) `(IN a (IDS ,frl-sp)) `(= ((STRAND-MAP ,frl-sp) a) ,(frl-rtrace 'u0 'v0 'v3)))
    (frl-and (append-map
               (lambda (j d m)
                 (list `(IN (LIST ,j a) (NODES ,frl-sp))
                       (if (eq? d 'SENT) `(IS-SENT ,frl-sp (LIST ,j a)) `(IS-RECEIVED ,frl-sp (LIST ,j a)))
                       `(= (NODE-CONTENT ,frl-sp (LIST ,j a)) ,m)))
               '(1 2 3) '(RECEIVED SENT RECEIVED) '(u0 v0 v3)))))))
(dk-peel!)
(frl-space!)
(let ((lit (frl-rtrace 'u0 'v0 'v3)))
  (fact 'three-strand-nodes frl-sp 'a (cadr lit) (caddr lit) (cadddr lit))
  (dk-split-all!)
  (frl-nth-all!)
  (dk-conj-close! frl-node-closer!))
(qed 'resp-trace-nodes)

;;; LEMMA 5.3, general: nb originates at the responder's second node, given nb @ l0 and not nb @ u0.
(sp (make-wff (frl-foralls '(nsp s u0 l0 ka kb nb)
  (frl-curry (list '(IS-PK-SPACE nsp) `(IN s (IDS ,frl-sp)) `(= ((STRAND-MAP ,frl-sp) s) ,(frl-rtrace 'u0 frl-v0* frl-v3*))
                   `(IN l0 (TUPLES ,frl-msgs)) `(IN ka ,frl-K) `(IN kb ,frl-K) `(IN nb ,frl-T)
                   `(IS-SUBTERM ,frl-T ,frl-K nb (LST l0)) `(NOT (IS-SUBTERM ,frl-T ,frl-K nb u0)))
    `(ORIGINATES ,frl-sp nb (LIST 2 s))))))
(dk-peel!)
(frl-space!)
(let ((lit (frl-rtrace 'u0 frl-v0* frl-v3*)))
  (fact 'list-in-msgs frl-T frl-K 'l0)
  (fact 'encr-in-msgs frl-T frl-K '(LST l0) 'ka)
  (fact 'token-in-msgs frl-T frl-K 'nb)
  (fact 'encr-in-msgs frl-T frl-K 'nb 'kb)
  (frl-fact-split! 'resp-trace-nodes 'nsp 's 'u0 frl-v0* frl-v3*)
  (fact 'subterm-encr frl-T frl-K 'nb '(LST l0) 'ka)
  (dk-have! `(IS-SUBTERM ,frl-T ,frl-K nb (NODE-CONTENT ,frl-sp (LIST 2 s)))
    (lambda () (frl-subst-ass! `(= (NODE-CONTENT ,frl-sp (LIST 2 s)) ,frl-v0*))))
  (dk-have! `(FORALL m (IMPLIES (SAME-STRAND-BEFORE ,frl-sp m (LIST 2 s)) (NOT (IS-SUBTERM ,frl-T ,frl-K nb (NODE-CONTENT ,frl-sp m)))))
    (lambda ()
      (let ((m (caddr (find-first (lambda (f) (dk-head-is? f 'SAME-STRAND-BEFORE)) (dk-peel!)))))
        (di)
        (frl-project! 'same-strand-before `(SAME-STRAND-BEFORE ,frl-sp ,m (LIST 2 s))
          `(AND (IN ,m (NODES ,frl-sp)) (AND (IN (LIST 2 s) (NODES ,frl-sp)) (AND (= (NTH 2 ,m) (NTH 2 (LIST 2 s))) (< (NTH 1 ,m) (NTH 1 (LIST 2 s)))))))
        (dk-split-all!)
        (dk-nth-h! `(= (NTH 2 ,m) (NTH 2 (LIST 2 s))))
        (dk-nth-h! `(< (NTH 1 ,m) (NTH 1 (LIST 2 s))))
        (frl-fact-split! 'node-parts frl-sp m)
        (dk-rewrite-h! `(= ((STRAND-MAP ,frl-sp) s) ,lit) 's `(NTH 2 ,m))
        (frl-or-each! (dk-cite! 'three-strand-node frl-sp m (cadr lit) (caddr lit) (cadddr lit))
          (lambda (d)
            (dk-split-all!)
            (frl-nth-all!)
            (let ((j (caddr (cadr d))))
              (if (> j 1)
                  (frl-nn-absurd! `(= (NTH 1 ,m) ,j) `(< (NTH 1 ,m) 2))
                  (begin
                    (dk-rewrite-h! `(IS-SUBTERM ,frl-T ,frl-K nb (NODE-CONTENT ,frl-sp ,m)) `(NODE-CONTENT ,frl-sp ,m) 'u0)
                    (ai `(NOT (IS-SUBTERM ,frl-T ,frl-K nb u0)))))))))))
  (fact 'originates-intro frl-sp 'nb '(LIST 2 s))
  (dk-ass!))
(qed 'flat-resp-nonce-originates)

;; the hypotheses of Proposition 5.2, over a flat space and the general responder trace
(define (frl-H-resp body)
  (frl-foralls '(nsp c s u0 l0 ka kb nb)
    (frl-curry (list '(IS-FLAT-REGULAR nsp) '(IS-BUNDLE c) `(= (BSPACE c) ,frl-sp)
                     `(IN s (IDS ,frl-sp)) `(= ((STRAND-MAP ,frl-sp) s) ,(frl-rtrace 'u0 frl-v0* frl-v3*))
                     '(IN (LIST 3 s) (BNODES c))
                     `(NOT (IN ((KINV ,frl-sp) ka) (ADV-TOKENS (PK-INF nsp))))
                     `(IN l0 (TUPLES ,frl-msgs)) `(IN ka ,frl-K) `(IN kb ,frl-K) `(IN nb ,frl-T) `(NOT (IN nb ,frl-K))
                     `(IS-SUBTERM ,frl-T ,frl-K nb (LST l0)) `(NOT (IS-SUBTERM ,frl-T ,frl-K nb u0))
                     `(UNIQUELY-ORIGINATES ,frl-sp nb))
      body)))
(define (frl-conds-54 z) (list (frl-sub 'nb z) `(NOT ,(frl-sub frl-v0* z))))

(define (frl-resp-setup! conds-of)
  (frl-nsl-space!)
  (fact 'list-in-msgs frl-T frl-K 'l0)
  (fact 'encr-in-msgs frl-T frl-K '(LST l0) 'ka)
  (fact 'token-in-msgs frl-T frl-K 'nb)
  (fact 'encr-in-msgs frl-T frl-K 'nb 'kb)
  (frl-fact-split! 'resp-trace-nodes 'nsp 's 'u0 frl-v0* frl-v3*)
  (frl-D-incl!)
  (fact 'flat-resp-nonce-originates 'nsp 's 'u0 'l0 'ka 'kb 'nb)
  (fact 'subterm-refl frl-T frl-K frl-v0*)
  (dk-have! (frl-sub frl-v0* '(LIST 2 s)) (lambda () (frl-subst-ass! `(= ,(frl-c '(LIST 2 s)) ,frl-v0*))))
  (dk-have! `(NOT (IN (LIST 2 s) ,(frl-S conds-of)))
    (lambda () (di) (frl-open-S! conds-of '(LIST 2 s)) (ai `(NOT ,(frl-sub frl-v0* '(LIST 2 s)))))))

;; (= v0 v3) in context: absurd ({l0}_ka = {nb}_kb gives LST(l0) = nb, a token)
(define (frl-v0-v3-absurd!)
  (frl-fact-split! 'encr-injective '(LST l0) 'ka 'nb 'kb)
  (frl-token-eq-absurd! 'nb '(LST l0)))

;;; LEMMA 5.4, general.
(sp (make-wff (frl-H-resp
  `(FORSOME n2 ,(frl-and (append (frl-min-conjs frl-conds-54 'n2)
                                 (list `(IS-REGULAR-NODE ,frl-isp n2) `(IS-SENT ,frl-sp n2))))))))
(dk-peel!)
(frl-resp-setup! frl-conds-54)
(let* ((n3 '(LIST 3 s)))
  (frl-sub-fwd! 'nb frl-v3*)
  (dk-have! (frl-sub 'nb n3) (lambda () (frl-subst-ass! `(= ,(frl-c n3) ,frl-v3*))))
  (dk-have! `(NOT ,(frl-sub frl-v0* n3))
    (lambda ()
      (di)
      (dk-rewrite-h! (frl-sub frl-v0* n3) (frl-c n3) frl-v3*)
      (frl-in-D! 'nb)
      (frl-or-each! (dk-cite! 'subterm-of-flat-encr-token frl-T frl-K frl-D frl-v0* 'nb 'kb)
        (lambda (e) (if (dk-head-is? e '=) (frl-v0-v3-absurd!) (frl-D-absurd! frl-v0*))))))
  (let* ((r (frl-minimal! frl-conds-54 n3))
         (n2 (car r)) (univ (cdr r))
         (x (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c frl-sp (frl-S frl-conds-54) 'nb '(LIST 2 s) n2))))
    (frl-by-minimality! (frl-sub frl-v0* x) x univ)
    (use-em `(IS-ADVERSARY-NODE ,frl-isp ,n2)
      (lambda ()
        (let ((z (dk-skolem! (dk-cite! 'flat-adversary-loss 'nsp 'c n2 x '(LST l0) 'ka))))
          (for-each (lambda (p) (dk-rewrite-h! p (frl-c n2) (frl-c z))) (frl-conds-54 n2))
          (ai (dk-apply! univ z))))
      (lambda ()
        (dk-have! `(IS-REGULAR-NODE ,frl-isp ,n2)
          (lambda ()
            (mac 'is-regular-node)
            (di)
            (dk-have! `(IS-ADVERSARY-NODE ,frl-isp ,n2) (lambda () (mac 'is-adversary-node) (dk-ass!)))
            (ai `(NOT (IS-ADVERSARY-NODE ,frl-isp ,n2)))))
        (ew n2)
        (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "flat lemma 5.4: open" (dk-goal)))))))))
(qed 'flat-lemma-5-4)

;;; LEMMA 5.6, general (for the original protocol this is Lemma 5.9).
(sp (make-wff (frl-H-resp
  `(FORALL n2 ,(frl-curry (append (frl-min-conjs frl-conds-54 'n2) (list `(IS-REGULAR-NODE ,frl-isp n2) `(IS-SENT ,frl-sp n2)))
     `(FORSOME n1 (AND (SAME-STRAND-BEFORE ,frl-sp n1 n2) (= ,(frl-c 'n1) ,frl-v0*))))))))
(dk-peel!)
(frl-resp-setup! frl-conds-54)
(let* ((n2 'n2)
       (univ (frl-min-univ frl-conds-54 n2)))
  (frl-in-S! frl-conds-54 n2)
  (dk-have! `(FORALL z (IMPLIES (IN z ,(frl-S frl-conds-54)) (IN z (BNODES c))))
    (lambda () (let ((z (cadr (car (dk-peel!))))) (frl-open-S! frl-conds-54 z) (dk-ass!))))
  (let ((x (dk-skolem! (dk-cite! 'bundle-minimal-earlier 'c frl-sp (frl-S frl-conds-54) 'nb '(LIST 2 s) n2))))
    (frl-by-minimality! (frl-sub frl-v0* x) x univ)
    (frl-ssb-open-sp! x n2)
    (frl-regular-before! x n2)
    (fact 'flat-regular-encr-subterm 'nsp x '(LST l0) 'ka)
    (ew x)
    (dk-conj-close! (lambda () (if (not (dk-ass!)) (frl-subst-rfl! `(= ,frl-v0* ,(frl-c x))))))))
(qed 'flat-lemma-5-6)
