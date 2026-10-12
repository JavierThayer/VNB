;;; strand-adversary-bound.scm -- THE ADVERSARY BOUND (the paper's Proposition 3.3 on the user's
;;; model with encryption): a token the adversary does not know, and which originates on no regular
;;; node of a bundle, is a subterm of the content of NO node of the bundle.
;;; (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, section 3.2; the definitions are
;;;  structure-library/strand-adversary.scm.)  Agent S-2, week 3, 2026-10-06; the E and D cases
;;;  added by agent S-2b the same day (S-2's key-free version: archive/2026-10-06/s2b/).
;;;  Helper prefix: sab-.
;;;
;;; Every theorem bills `modulo 0'; the oracles are `arith' and `ineq' (NN arithmetic, dk-nn!).
;;;
;;; THE PAPER'S METHOD, which is the point: S = {n in C : t @ CONTENT(n)}; if S is nonempty it has a
;;; minimal member m (Lemma 2.7, `bundle-minimal'); m originates t (Lemma 2.9,
;;; `bundle-minimal-originates'), so it is SENT (Lemma 2.8); by hypothesis m is an ADVERSARY node,
;;; and the seven trace kinds are taken in turn -- one theorem each, which is what the NSL work
;;; and the paper's general bound (section 6.3) will cite:
;;;   text-trace-origin        an M node originates only tokens the adversary knows
;;;   flush-trace-no-sent      an F strand has no SENT node
;;;   tee-trace-no-origin      nothing originates on a T node
;;;   concat-trace-no-origin   no TOKEN originates on a C node (a token subterm of the sent list
;;;                            message is a subterm of a component, received earlier: the token law)
;;;   separate-trace-no-origin nothing originates on an S node (each sent component is a subterm
;;;                            of the list message received first)
;;;   encrypt-trace-no-origin  no TOKEN originates on an E node (a token below ENCR(m, k) is below
;;;                            m: the token law, and the key is not a subterm; m was received)
;;;   decrypt-trace-no-origin  nothing originates on a D node (a subterm of m is a subterm of
;;;                            ENCR(m, k), received earlier)
;;;   adversary-node-origin    the seven assembled: a token originating on an adversary node is known
;;;   adversary-bound          THE BOUND
;;;   adversary-bound-adversary-nodes   the paper's "in particular": no adversary node of C either.
;;; And encrypt-trace-strand, decrypt-trace-strand: the literal E and D strands of a key and a
;;; message are strands of the space and satisfy their trace predicates (S-2b).
;;; Plus nn-le-ne-succ (a <= k, k /= a give succ a <= k), the case-split brick of the index
;;; arithmetic on literal strands; and, for finding (g), sent-received-in-pair, directed-intro
;;; (a directed message is built from a message), separate-trace-exists and concat-trace-exists
;;; (every list of messages has an S and a C trace: `tuple-tabulation', CONS, an IF on the index).
;;;
;;; TWO DEFINEDNESS TRAPS MET (both leave the proof silently incomplete at `qed', no error at the
;;; step): an instantiation at DIRECTED(T) or at a def-by-nn-recursion term such as MSG-STAGE(T, 0)
;;; owes `t = t' unless the term already occurs in a true (IN _ _) hypothesis -- type it first; and
;;; `rfl' on a literal list [SENT, g] wants the list typed (directed-intro) before it is closed.
;;;
;;; THE INDEX ARITHMETIC IS THE COST.  A node is [k, p]; on a literal strand the entry at k is read
;;; by first deciding WHICH numeral k is (1 <= k <= 3 for a tee trace: two uses of nn-le-ne-succ),
;;; then `node-content-eq' and `nth-r'.  On the n-ary C and S traces the entry is read off the
;;; trace's universal at k, and k is split by `nn-le-succ-cases' (C) or `nn-pos-is-succ' (S).
;;;
;;; THE HYPOTHESIS-SIDE REWRITE.  The tree has no `subst' on a hypothesis; `sab-rewrite!' proves
;;; F => F[from := to] by rewriting its GOAL and detaches it -- every content computation here goes
;;; through it (the kit's owed "hypothesis-side rewrite", CLAUDE.md, is exactly this).
;;;
;;; LOAD WINDOW: after theorem-library/strand-space-laws and structure-library/strand-adversary;
;;; nn-le-succ-cases (nn-order-ord), nn-lt-succ-le (finite-surgery), nn-pos-is-succ, nn-one-in.

;;; -----------------------------------------------------------------------
;;; helpers (prefix sab-)

(define (sab-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(sab-and (cdr fs)))))
(define (sab-have-and! . fs)
  (let ((c (sab-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (ass)))))
    c))

;; F in context, (== FROM TO) or (= FROM TO) in context: land F[FROM := TO].
(define (sab-rewrite! f from to)
  (let* ((f2 (dk--replace f from to))
         (imp `(IMPLIES ,f ,f2)))
    (dk-have! imp (lambda () (subst `(= ,from ,to)) (di) (ass)))
    (detach! imp)
    f2))

;; F in context: land F with every NTH of a literal list reduced.
(define (sab-nth! f)
  (let* ((f2 (reduce-nth-in-expr f))
         (imp `(IMPLIES ,f ,f2)))
    (if (equal? f2 f)
        f
        (begin
          (dk-have! imp (lambda () (nth-r) (di) (ass)))
          (detach! imp)
          f2))))

(define (sab-sigma spa n) `((STRAND-MAP ,spa) (NTH 2 ,n)))

;; The node N's content and direction equations at index K with entry D (both (= (NTH 1 N) K)
;; -- proved by rfl when K is (NTH 1 N) itself -- and (= (NTH K SIGMA) D) in context), reduced;
;; returns (content-eq dir-eq).
(define (sab-entry! spa n k d)
  (if (not (dk-asm? `(= (NTH 1 ,n) ,k))) (dk-have! `(= (NTH 1 ,n) ,k) (lambda () (rfl))))
  (fact 'node-content-eq spa n k d)
  (let* ((ce `(== (NODE-CONTENT ,spa ,n) (NTH 2 ,d)))
         (de `(== (NODE-DIR ,spa ,n) (NTH 1 ,d))))
    (dk-split-all!)
    (list (sab-nth! ce) (sab-nth! de))))

;; (IS-SENT spa n) in context and (== (NODE-DIR spa n) RECEIVED): close the focus goal.
(define (sab-received-absurd! spa n)
  (dk-have! `(= (NODE-DIR ,spa ,n) SENT) (lambda () (mac-h 'is-sent `(IS-SENT ,spa ,n)) (ass)))
  (dk-have! '(= SENT RECEIVED)
    (lambda () (subst `(= SENT (NODE-DIR ,spa ,n))) (subst `(= (NODE-DIR ,spa ,n) RECEIVED)) (rfl)))
  (fact 'sent-ne-received)
  (ai '(NOT (= SENT RECEIVED))))

;; (= (LENGTH sigma) K) from (= sigma LIT) in context.
(define (sab-len-eq! sg lit k)
  (dk-have! `(= (LENGTH ,sg) ,k) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl))))

;; The common close: the node N2 = [J, NTH(2, N)] comes before N on its strand, its entry is DJ
;; (proved by ENTRY-THUNK on the goal (= (NTH J sigma) DJ), sigma the strand of N), its content
;; GJ has u as a subterm (in context), and NOEARLY says no earlier node's content does.  The
;; typings J in NN, 1 <= J, J <= LENGTH(sigma) must be in context; LT-PREMS prove J < NTH(1, N).
(define (sab-earlier! spa n j dj gj noearly entry-thunk lt-prems)
  (let ((n2 `(LIST ,j (NTH 2 ,n)))
        (sg (sab-sigma spa n)))
    (fact 'node-intro spa j `(NTH 2 ,n))
    (dk-have! `(SAME-STRAND-BEFORE ,spa ,n2 ,n)
      (lambda ()
        (mac 'same-strand-before)
        (nth-r)
        (dk-conj-close!
          (lambda ()
            (cond ((dk-asm? (dk-goal)) (ass))
                  ((dk-head-is? (dk-goal) '=) (rfl))
                  (#t (apply dk-nn! lt-prems)))))))
    (dk-have! `(= (NTH 1 ,n2) ,j) (lambda () (nth-r) (rfl)))
    (dk-have! `(= (NTH ,j ((STRAND-MAP ,spa) (NTH 2 ,n2))) ,dj) (lambda () (nth-r) (entry-thunk)))
    (let ((ce (car (sab-entry! spa n2 j dj))))
      (dk-have! `(IS-SUBTERM (TOKENS ,spa) (KEYS ,spa) u (NODE-CONTENT ,spa ,n2))
        (lambda () (subst `(= (NODE-CONTENT ,spa ,n2) ,gj)) (ass)))
      (ai (dk-apply! noearly n2)))))

;; The parts of the strand space, the node N and the origination of u at N, landed; returns the
;; no-earlier universal.
(define (sab-setup! spa n)
  (fact 'strand-space-parts spa)
  (dk-split-all!)
  (fact 'node-parts spa n)
  (dk-split-all!)
  (fact 'strand-at-id spa `(NTH 2 ,n))
  (fact 'length-in-nn `(DIRECTED (TOKENS ,spa) (KEYS ,spa)) (sab-sigma spa n))
  (if (dk-asm? `(ORIGINATES ,spa u ,n))
      (begin
        (fact 'originates-elim spa 'u n)
        (dk-split-all!)
        (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SAME-STRAND-BEFORE)))
                 "no earlier node"))
      #f))

;;; -----------------------------------------------------------------------
;;; The case-split brick.

;;; nn-le-ne-succ (a <= k, k /= a  =>  succ a <= k) MOVED to theorem-library/finite-surgery.scm
;;; (2026-10-07: an NN order lemma in the strand file, now cited by the kit's dk-subterm-literal!).

;;; -----------------------------------------------------------------------
;;; The five key-free trace kinds (S-2).

(sp (make-wff '(FORALL spa (FORALL P (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa)
  (IMPLIES (FORALL x (IMPLIES (IN x P) (IN x (TOKENS spa))))
  (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-TEXT-TRACE spa P ((STRAND-MAP spa) (NTH 2 n)))
  (IMPLIES (ORIGINATES spa u n) (IN u P))))))))))))
(let* ((landed (dk-peel!))
       (incl (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'TOKENS))) landed))
       (sg (sab-sigma 'spa 'n)))
  (sab-setup! 'spa 'n)
  (mac-h 'is-text-trace `(IS-TEXT-TRACE spa P ,sg))
  (let* ((a (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the text")))
         (lit `(LIST (LIST SENT ,a))))
    (sab-len-eq! sg lit 1)
    (dk-have! '(= (NTH 1 n) 1) (lambda () (dk-nn! '(<= 1 (NTH 1 n)) `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) 1))))
    (dk-have! `(= (NTH 1 ,sg) (LIST SENT ,a)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
    (sab-entry! 'spa 'n 1 `(LIST SENT ,a))
    (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) a)
    (dk-apply! incl a)
    (fact 'subterm-of-token '(TOKENS spa) '(KEYS spa) 'u a)
    (subst `(= u ,a))
    (ass)))
(qed 'text-trace-origin)

(sp (make-wff '(FORALL spa (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-FLUSH-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (IS-SENT spa n)))))))))
(dk-peel!)
(di)
(let ((sg (sab-sigma 'spa 'n)))
  (sab-setup! 'spa 'n)
  (mac-h 'is-flush-trace `(IS-FLUSH-TRACE spa ,sg))
  (let* ((g (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message")))
         (lit `(LIST (LIST RECEIVED ,g))))
    (sab-len-eq! sg lit 1)
    (dk-have! '(= (NTH 1 n) 1) (lambda () (dk-nn! '(<= 1 (NTH 1 n)) `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) 1))))
    (dk-have! `(= (NTH 1 ,sg) (LIST RECEIVED ,g)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
    (sab-entry! 'spa 'n 1 `(LIST RECEIVED ,g))
    (sab-received-absurd! 'spa 'n)))
(qed 'flush-trace-no-sent)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-TEE-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (ORIGINATES spa u n))))))))))
(dk-peel!)
(di)
(let* ((sg (sab-sigma 'spa 'n))
       (noearly (sab-setup! 'spa 'n)))
  (mac-h 'is-tee-trace `(IS-TEE-TRACE spa ,sg))
  (let* ((g (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message")))
         (lit `(LIST (LIST RECEIVED ,g) (LIST SENT ,g) (LIST SENT ,g)))
         (entry (lambda (j d) (dk-have! `(= (NTH ,j ,sg) ,d) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))))
         ;; the node at index J >= 2 carries g, received at index 1
         (sent-case
           (lambda (j)
             (entry j `(LIST SENT ,g))
             (let ((ce (car (sab-entry! 'spa 'n j `(LIST SENT ,g)))))
               (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) g)
               (fact 'nn-one-in)
               (dk-have! '(<= 1 1) (lambda () (dk-nn!)))
               (dk-have! `(<= 1 (LENGTH ,sg)) (lambda () (dk-nn! `(= (LENGTH ,sg) 3))))
               (sab-earlier! 'spa 'n 1 `(LIST RECEIVED ,g) g noearly
                 (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl))
                 (list '(<= (succ 1) (NTH 1 n))))))))
    (sab-len-eq! sg lit 3)
    (use-em '(= (NTH 1 n) 1)
      (lambda ()
        (entry 1 `(LIST RECEIVED ,g))
        (sab-entry! 'spa 'n 1 `(LIST RECEIVED ,g))
        (sab-received-absurd! 'spa 'n))
      (lambda ()
        (fact 'nn-one-in)
        (fact 'nn-le-ne-succ 1 '(NTH 1 n))
        (use-em '(= (NTH 1 n) 2)
          (lambda () (sent-case 2))
          (lambda ()
            (dk-have! '(IN 2 NN) (lambda () (arith)))
            (dk-have! '(<= 2 (NTH 1 n)) (lambda () (dk-nn! '(<= (succ 1) (NTH 1 n)))))
            (fact 'nn-le-ne-succ 2 '(NTH 1 n))
            (dk-have! '(= (NTH 1 n) 3)
              (lambda () (dk-nn! '(<= (succ 2) (NTH 1 n)) `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) 3))))
            (sent-case 3)))))))
(qed 'tee-trace-no-origin)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN u (TOKENS spa))
  (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-CONCAT-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (ORIGINATES spa u n)))))))))))
(dk-peel!)
(di)
(let* ((sg (sab-sigma 'spa 'n))
       (noearly (sab-setup! 'spa 'n)))
  (mac-h 'is-concat-trace `(IS-CONCAT-TRACE spa ,sg))
  (let* ((l (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list")))
         (len `(LENGTH ,l))
         (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'RECEIVED))) "the received entries")))
    (fact 'length-in-nn '(MSG-SET (TOKENS spa) (KEYS spa)) l)
    (dk-have! `(<= (NTH 1 n) (succ ,len))
      (lambda () (dk-nn! `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) (succ ,len)))))
    (let ((o (dk-cite! 'nn-le-succ-cases len '(NTH 1 n))))
      (dk-each-leaf! (lambda () (ai o))
        (lambda ()
          (if (dk-asm? `(<= (NTH 1 n) ,len))
              ;; a received node
              (let ((d `(LIST RECEIVED (NTH (NTH 1 n) ,l))))
                (dk-apply! univ '(NTH 1 n))
                (sab-entry! 'spa 'n '(NTH 1 n) d)
                (sab-received-absurd! 'spa 'n))
              ;; the sent node: the list l, whose token subterm sits in a component received earlier
              (let ((d `(LIST SENT (LST ,l))))
                (dk-have! `(= (NTH (succ ,len) ,sg) ,d) (lambda () (ass)))
                (sab-entry! 'spa 'n `(succ ,len) d)
                (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) `(LST ,l))
                (let* ((ex (dk-cite! 'token-subterm-of-list '(TOKENS spa) '(KEYS spa) 'u l))
                       (i (dk-skolem! ex)))
                  (dk-apply! univ i)
                  (dk-have! `(<= ,i (LENGTH ,sg)) (lambda () (dk-nn! `(<= ,i ,len) `(= (LENGTH ,sg) (succ ,len)))))
                  (sab-earlier! 'spa 'n i `(LIST RECEIVED (NTH ,i ,l)) `(NTH ,i ,l) noearly
                    (lambda () (ass))
                    (list `(<= ,i ,len) `(= (NTH 1 n) (succ ,len))))))))))))
(qed 'concat-trace-no-origin)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-SEPARATE-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (ORIGINATES spa u n))))))))))
(dk-peel!)
(di)
(let* ((sg (sab-sigma 'spa 'n))
       (noearly (sab-setup! 'spa 'n)))
  (mac-h 'is-separate-trace `(IS-SEPARATE-TRACE spa ,sg))
  (let* ((l (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the list")))
         (len `(LENGTH ,l))
         (univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SENT) (dk-contains? f l))) "the sent entries")))
    (fact 'length-in-nn '(MSG-SET (TOKENS spa) (KEYS spa)) l)
    (use-em '(= (NTH 1 n) 1)
      ;; the received node
      (lambda ()
        (sab-entry! 'spa 'n 1 `(LIST RECEIVED (LST ,l)))
        (sab-received-absurd! 'spa 'n))
      ;; a sent node: index succ q, carrying the q-th component of the list received at index 1
      (lambda ()
        (let* ((q (dk-skolem! (dk-cite! 'nn-pos-is-succ '(NTH 1 n)))))
          (dk-have! `(NOT (= ,q 0))
            (lambda ()
              (di)
              (dk-have! '(= (NTH 1 n) 1)
                (lambda () (subst `(= (NTH 1 n) (succ ,q))) (subst `(= ,q 0)) (arith)))
              (ai '(NOT (= (NTH 1 n) 1)))))
          (fact 'nn-zero-in)
          (fact 'nn-zero-le q)
          (fact 'nn-le-ne-succ 0 q)
          (dk-have! `(<= 1 ,q) (lambda () (dk-nn! `(<= (succ 0) ,q))))
          (dk-have! `(<= ,q ,len)
            (lambda () (dk-nn! `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) (succ ,len)) `(= (NTH 1 n) (succ ,q)))))
          (dk-apply! univ q)
          (sab-entry! 'spa 'n `(succ ,q) `(LIST SENT (NTH ,q ,l)))
          (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) `(NTH ,q ,l))
          (fact 'subterm-component '(TOKENS spa) '(KEYS spa) 'u l q)
          (fact 'nn-one-in)
          (dk-have! '(<= 1 1) (lambda () (dk-nn!)))
          (dk-have! `(<= 1 (LENGTH ,sg)) (lambda () (dk-nn! `(= (LENGTH ,sg) (succ ,len)))))
          (sab-earlier! 'spa 'n 1 `(LIST RECEIVED (LST ,l)) `(LST ,l) noearly
            (lambda () (ass))
            (list `(= (NTH 1 n) (succ ,q)) `(<= 1 ,q)))))))
  )
(qed 'separate-trace-no-origin)

;;; THE TWO KEY-BEARING TRACES (S-2b).  E: [received k, received m, sent ENCR(m, k)] -- a token
;;; below the sent encryption is below m (the token law: it is not the encryption; the convention:
;;; the key is not a subterm), and m was received at index 2.  D: [received KINV(k), received
;;; ENCR(m, k), sent m] -- anything below m is below ENCR(m, k), received at index 2.

;; A literal three-entry strand LIT equal to SG: the node n is at index 1, 2 or 3; RECEIVED-AT
;; lists the received indices (closed by the direction), SENT-CASE is called at the sent index 3.
(define (sab-three! sg lit sent-case)
  (let ((entry (lambda (j) (dk-have! `(= (NTH ,j ,sg) ,(list-ref lit j)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))))
        (received (lambda (j)
                    (dk-have! `(= (NTH ,j ,sg) ,(list-ref lit j)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
                    (sab-entry! 'spa 'n j (list-ref lit j))
                    (sab-received-absurd! 'spa 'n))))
    (sab-len-eq! sg lit 3)
    (use-em '(= (NTH 1 n) 1)
      (lambda () (received 1))
      (lambda ()
        (fact 'nn-one-in)
        (fact 'nn-le-ne-succ 1 '(NTH 1 n))
        (use-em '(= (NTH 1 n) 2)
          (lambda () (received 2))
          (lambda ()
            (dk-have! '(IN 2 NN) (lambda () (arith)))
            (dk-have! '(<= 2 (NTH 1 n)) (lambda () (dk-nn! '(<= (succ 1) (NTH 1 n)))))
            (fact 'nn-le-ne-succ 2 '(NTH 1 n))
            (dk-have! '(= (NTH 1 n) 3)
              (lambda () (dk-nn! '(<= (succ 2) (NTH 1 n)) `(<= (NTH 1 n) (LENGTH ,sg)) `(= (LENGTH ,sg) 3))))
            (entry 3)
            (sab-entry! 'spa 'n 3 (list-ref lit 3))
            (dk-have! '(<= 1 2) (lambda () (dk-nn!)))
            (dk-have! `(<= 2 (LENGTH ,sg)) (lambda () (dk-nn! `(= (LENGTH ,sg) 3))))
            (sent-case (lambda (gj noearly)
                         (sab-earlier! 'spa 'n 2 (list-ref lit 2) gj noearly
                           (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl))
                           (list '(= (NTH 1 n) 3)))))))))))

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN u (TOKENS spa))
  (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-ENCRYPT-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (ORIGINATES spa u n)))))))))))
(dk-peel!)
(di)
(let* ((sg (sab-sigma 'spa 'n))
       (noearly (sab-setup! 'spa 'n)))
  (mac-h 'is-encrypt-trace `(IS-ENCRYPT-TRACE spa ,sg))
  (let* ((k (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the key")))
         (m (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message")))
         (lit `(LIST (LIST RECEIVED ,k) (LIST RECEIVED ,m) (LIST SENT (ENCR ,m ,k)))))
    (fact 'encr-in-msgs '(TOKENS spa) '(KEYS spa) m k)
    (sab-three! sg lit
      (lambda (earlier!)
        (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) `(ENCR ,m ,k))
        (fact 'token-subterm-of-encr '(TOKENS spa) '(KEYS spa) 'u m k)
        (earlier! m noearly)))))
(qed 'encrypt-trace-no-origin)

(sp (make-wff '(FORALL spa (FORALL u (FORALL n (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN n (NODES spa))
  (IMPLIES (IS-DECRYPT-TRACE spa ((STRAND-MAP spa) (NTH 2 n))) (NOT (ORIGINATES spa u n))))))))))
(dk-peel!)
(di)
(let* ((sg (sab-sigma 'spa 'n))
       (noearly (sab-setup! 'spa 'n)))
  (mac-h 'is-decrypt-trace `(IS-DECRYPT-TRACE spa ,sg))
  (let* ((k (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the key")))
         (m (dk-skolem! (dk-pick (lambda (f) (dk-head-is? f 'FORSOME)) "the message")))
         (lit `(LIST (LIST RECEIVED ((KINV spa) ,k)) (LIST RECEIVED (ENCR ,m ,k)) (LIST SENT ,m))))
    (fact 'encr-in-msgs '(TOKENS spa) '(KEYS spa) m k)
    (sab-three! sg lit
      (lambda (earlier!)
        (sab-rewrite! '(IS-SUBTERM (TOKENS spa) (KEYS spa) u (NODE-CONTENT spa n)) '(NODE-CONTENT spa n) m)
        (fact 'subterm-encr '(TOKENS spa) '(KEYS spa) 'u m k)
        (earlier! `(ENCR ,m ,k) noearly)))))
(qed 'decrypt-trace-no-origin)

;; An OR in context, split to its leaves (right-nested); HANDLER gets the disjunct of each leaf.
(define (sab-or-each! o handler)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((dk-head-is? (caddr o) 'OR) (sab-or-each! (caddr o) handler))
            (#t (handler (caddr o)))))))

;;; -----------------------------------------------------------------------
;;; The seven assembled, and the bound.

;; Land the projection CLAIM of the predicate hypothesis HYP on a lane.
(define (sab-project! pred hyp claim)
  (dk-have! claim (lambda () (mac-h pred hyp) (dk-split-all!) (ass)))
  claim)

(define (sab-isp-laws! isp)
  (let ((h `(IS-INFILTRATED-SPACE ,isp)))
    (sab-project! 'is-infiltrated-space h `(IS-STRAND-SPACE (ISPACE ,isp)))
    (sab-project! 'is-infiltrated-space h
      `(FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS ,isp)) (IN sat_ (TOKENS (ISPACE ,isp))))))
    (sab-project! 'is-infiltrated-space h
      `(FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS ,isp))
         (IS-ADVERSARY-TRACE (ISPACE ,isp) (ADV-TOKENS ,isp) ((STRAND-MAP (ISPACE ,isp)) sap_)))))))

(sp (make-wff '(FORALL isp (FORALL u (FORALL n (IMPLIES (IS-INFILTRATED-SPACE isp)
  (IMPLIES (IN u (TOKENS (ISPACE isp))) (IMPLIES (IN n (NODES (ISPACE isp))) (IMPLIES (IS-ADVERSARY-NODE isp n)
  (IMPLIES (ORIGINATES (ISPACE isp) u n) (IN u (ADV-TOKENS isp))))))))))))
(dk-peel!)
(sab-isp-laws! 'isp)
(let* ((spa '(ISPACE isp))
       (pp '(ADV-TOKENS isp))
       (sg (sab-sigma spa 'n))
       (adv (sab-project! 'is-adversary-node '(IS-ADVERSARY-NODE isp n) '(IN (NTH 2 n) (ADV-IDS isp))))
       (tr (dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'IS-ADVERSARY-TRACE))) "the trace law")
                      '(NTH 2 n))))
  ;; META round 3: the IS-ADVERSARY-TRACE unfold instantiates at the strand
  ;; (STRAND-MAP (ISPACE isp))(NTH 2 n), which owes definedness unless typed: land
  ;; the node's parts and the strand's typing first, as sab-setup! does.
  (fact 'strand-space-parts spa)
  (dk-split-all!)
  (fact 'node-parts spa 'n)
  (dk-split-all!)
  (fact 'strand-at-id spa '(NTH 2 n))
  (mac-h 'is-adversary-trace tr)
  (sab-or-each! (dk-pick (lambda (f) (and (dk-head-is? f 'OR) (dk-contains? f 'IS-TEXT-TRACE))) "the seven kinds")
    (lambda (d)
      (case (car d)
        ((IS-TEXT-TRACE)
         (fact 'text-trace-origin spa pp 'u 'n)
         (ass))
        ((IS-FLUSH-TRACE)
         (fact 'originates-sent spa 'u 'n)
         (dk-split-all!)
         (ai (dk-cite! 'flush-trace-no-sent spa 'n)))
        ((IS-TEE-TRACE) (ai (dk-cite! 'tee-trace-no-origin spa 'u 'n)))
        ((IS-CONCAT-TRACE) (ai (dk-cite! 'concat-trace-no-origin spa 'u 'n)))
        ((IS-SEPARATE-TRACE) (ai (dk-cite! 'separate-trace-no-origin spa 'u 'n)))
        ((IS-ENCRYPT-TRACE) (ai (dk-cite! 'encrypt-trace-no-origin spa 'u 'n)))
        ((IS-DECRYPT-TRACE) (ai (dk-cite! 'decrypt-trace-no-origin spa 'u 'n)))
        ((FALSITY) (error "adversary-node-origin: an unexpected kind" (expression->string d)))))))
(qed 'adversary-node-origin)

;;; THE BOUND (Proposition 3.3, key-free).  C is a bundle of the infiltrated space isp (its space
;;; is ISPACE(isp)); u is a token the adversary does not know; u originates on no regular node of
;;; C.  Then u is a subterm of the content of no node of C.
(sp (make-wff '(FORALL isp (FORALL c (FORALL u (IMPLIES (IS-INFILTRATED-SPACE isp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) (ISPACE isp))
  (IMPLIES (IN u (TOKENS (ISPACE isp))) (IMPLIES (NOT (IN u (ADV-TOKENS isp)))
  (IMPLIES (FORALL n (IMPLIES (IN n (BNODES c)) (IMPLIES (IS-REGULAR-NODE isp n) (NOT (ORIGINATES (ISPACE isp) u n)))))
    (FORALL n (IMPLIES (IN n (BNODES c))
      (NOT (IS-SUBTERM (TOKENS (ISPACE isp)) (KEYS (ISPACE isp)) u (NODE-CONTENT (ISPACE isp) n))))))))))))))))
(let* ((landed (dk-peel!))
       (reg (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'IS-REGULAR-NODE))) landed))
       (spa '(ISPACE isp))
       (n0 (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BNODES c)))) landed)))
       (ss `(SEP sbz_ (BNODES c) (IS-SUBTERM (TOKENS ,spa) (KEYS ,spa) u (NODE-CONTENT ,spa sbz_))))
       (eqn '(= (BSPACE c) (ISPACE isp))))
  (di)                                        ; u @ CONTENT(n0); goal FALSITY
  (dk-have! `(FORALL z (IMPLIES (IN z ,ss) (IN z (BNODES c))))
    (lambda () (dk-peel!) (sep-me (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) ss))) (dk-asms))) (ass)))
  (dk-have! `(FORSOME w (IN w ,ss)) (lambda () (ew n0) (in-sep! (lambda () (ass)) (lambda () (ass)))))
  ;; the minimal member m of S (Lemma 2.7)
  (let* ((m (dk-skolem! (dk-cite! 'bundle-minimal 'c ss)))
         (minS (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f m) (dk-contains? f 'PRECEDES-STRICT)))
                        "m minimal")))
    (dk-have! `(IN ,m (BNODES c)) (lambda () (sep-me `(IN ,m ,ss)) (ass)))
    (dk-have! `(IS-SUBTERM (TOKENS (BSPACE c)) (KEYS (BSPACE c)) u (NODE-CONTENT (BSPACE c) ,m))
      (lambda () (subst eqn) (sep-me `(IN ,m ,ss)) (ass)))
    (dk-have! `(FORALL z (IMPLIES (IN z (BNODES c)) (IMPLIES (IS-SUBTERM (TOKENS (BSPACE c)) (KEYS (BSPACE c)) u (NODE-CONTENT (BSPACE c) z))
                 (NOT (IN (LIST z ,m) (PRECEDES-STRICT c))))))
      (lambda ()
        (subst eqn)
        (dk-peel!)
        (let ((z (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BNODES c))
                                                    (not (equal? (cadr f) m)) (not (equal? (cadr f) n0))))
                                   (dk-asms)))))
          (dk-have! `(IN ,z ,ss) (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))
          (dk-apply! minS z)
          (ass))))
    ;; m originates u (Lemmas 2.8, 2.9), on the space of isp
    (fact 'bundle-minimal-originates 'c 'u m)
    (let ((orig (sab-rewrite! `(ORIGINATES (BSPACE c) u ,m) '(BSPACE c) spa)))
      (fact 'bundle-space 'c)
      (dk-apply! (dk-cite! 'bundle-nodes-in-space 'c) m)
      (sab-rewrite! `(IN ,m (NODES (BSPACE c))) '(BSPACE c) spa)
      (use-em `(IS-ADVERSARY-NODE isp ,m)
        ;; an adversary node: u is known, against the hypothesis
        (lambda ()
          (fact 'adversary-node-origin 'isp 'u m)
          (ai '(NOT (IN u (ADV-TOKENS isp)))))
        ;; a regular node: u does not originate there, against Lemma 2.9
        (lambda ()
          (dk-have! `(IS-REGULAR-NODE isp ,m)
            (lambda ()
              (mac 'is-regular-node)
              (di)
              (dk-have! `(IS-ADVERSARY-NODE isp ,m) (lambda () (mac 'is-adversary-node) (ass)))
              (ai `(NOT (IS-ADVERSARY-NODE isp ,m)))))
          (ai (dk-apply! reg m)))))))
(qed 'adversary-bound)

;;; The paper's "in particular": for an adversary node p of C, u is not a subterm of CONTENT(p).
(sp (make-wff '(FORALL isp (FORALL c (FORALL u (IMPLIES (IS-INFILTRATED-SPACE isp) (IMPLIES (IS-BUNDLE c)
  (IMPLIES (= (BSPACE c) (ISPACE isp))
  (IMPLIES (IN u (TOKENS (ISPACE isp))) (IMPLIES (NOT (IN u (ADV-TOKENS isp)))
  (IMPLIES (FORALL n (IMPLIES (IN n (BNODES c)) (IMPLIES (IS-REGULAR-NODE isp n) (NOT (ORIGINATES (ISPACE isp) u n)))))
    (FORALL n (IMPLIES (IN n (BNODES c)) (IMPLIES (IS-ADVERSARY-NODE isp n)
      (NOT (IS-SUBTERM (TOKENS (ISPACE isp)) (KEYS (ISPACE isp)) u (NODE-CONTENT (ISPACE isp) n)))))))))))))))))
(let* ((landed (dk-peel!))
       (n (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(BNODES c)))) landed))))
  (dk-apply! (dk-cite! 'adversary-bound 'isp 'c 'u) n)
  (dk-ass!))
(qed 'adversary-bound-adversary-nodes)


;; (IN (NTH i l) (MSG-SET (TOKENS spa) (KEYS spa))) from i in NN, 1 <= i, i <= LENGTH(l), l in TUPLES(MSG-SET (TOKENS spa) (KEYS spa)) in context.
(define (sml-nth-in-sab! i)
  (let ((goal `(IN (NTH ,i l) (MSG-SET (TOKENS spa) (KEYS spa)))))
    (if (not (dk-asm? goal))
        (begin
          (sab-have-and! `(IN ,i NN) '(IN l (TUPLES (MSG-SET (TOKENS spa) (KEYS spa)))) `(<= 1 ,i) `(<= ,i (LENGTH l)))
          (fact 'nth-in-range '(MSG-SET (TOKENS spa) (KEYS spa)) i 'l)))
    goal))

;;; -----------------------------------------------------------------------
;;; EXISTENCE of the n-ary traces (finding (g)): for every list l of messages there IS a
;;; separation trace and a concatenation trace, built by `tuple-tabulation' (the S trace as
;;; CONS of the received list onto the tabulated sent components; the C trace tabulated over
;;; succ(LENGTH l) by an IF on the index).  No list law was missing.

(sp (make-wff '(AND (IN SENT (PAIR SENT RECEIVED)) (IN RECEIVED (PAIR SENT RECEIVED)))))
(dk-have! '(IN SENT SET)
  (lambda () (subst (dk-cite! 'sent-def)) (fact 'nn-zero-in) (fact 'membership-implies-sethood 0 'NN) (ass)))
(dk-have! '(IN RECEIVED SET)
  (lambda () (subst (dk-cite! 'received-def)) (fact 'nn-one-in) (fact 'membership-implies-sethood 1 'NN) (ass)))
(sab-have-and! '(IN SENT SET) '(IN RECEIVED SET))
(fact 'pairing-membership 'SENT 'RECEIVED)
(let ((univ (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-head-is? (caddr f) 'IFF) (dk-contains? f 'RECEIVED)))
                     "the pairing universal")))
  (dk-conj-close!
    (lambda ()
      (let* ((v (cadr (dk-goal))) (iff (dk-apply! univ v)))
        (dk-have! `(OR (= ,v SENT) (= ,v RECEIVED))
          (lambda () (if (eq? v 'SENT) (oi-l) (oi-r)) (rfl)))
        (dk-only! iff `(OR (= ,v SENT) (= ,v RECEIVED)))
        (prop)))))
(qed 'sent-received-in-pair)

(sp (make-wff '(FORALL T (FORALL K (FORALL g (IMPLIES (IN g (MSG-SET T K))
   (AND (IN (LIST SENT g) (DIRECTED T K)) (IN (LIST RECEIVED g) (DIRECTED T K)))))))))
(dk-peel!)
(fact 'sent-received-in-pair)
(dk-split-all!)
(dk-conj-close!
  (lambda ()
    (mac 'DIRECTED)
    (let ((d (cadr (cadr (dk-goal)))))
      (fact 'pair-in-cartesian '(PAIR SENT RECEIVED) '(MSG-SET T K) d 'g)
      (ass))))
(qed 'directed-intro)

;; (IN (LIST dir g) (DIRECTED (TOKENS spa) (KEYS spa))) from (IN g (MSG-SET (TOKENS spa) (KEYS spa)))
;; in context (spa is the existence theorems' space).
(define (sab-directed! dir g)
  (fact 'directed-intro '(TOKENS spa) '(KEYS spa) g)
  (dk-split-all!)
  `(IN (LIST ,dir ,g) (DIRECTED (TOKENS spa) (KEYS spa))))

(sp (make-wff '(FORALL spa (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET (TOKENS spa) (KEYS spa))))
   (FORSOME s (AND (IN s (STRANDS (TOKENS spa) (KEYS spa))) (IS-SEPARATE-TRACE spa s))))))))
(dk-peel!)
(let* ((aa '(DIRECTED (TOKENS spa) (KEYS spa)))
       (len '(LENGTH l))
       (f '(VNB-LAMBDA sev_ NN (LIST SENT (NTH sev_ l))))
       (hyp `(FORALL sei_ (IMPLIES (AND (IN sei_ NN) (AND (<= 1 sei_) (<= sei_ ,len))) (IN (,f sei_) ,aa)))))
  (fact 'length-in-nn '(MSG-SET (TOKENS spa) (KEYS spa)) 'l)
  (fact 'list-in-msgs '(TOKENS spa) '(KEYS spa) 'l)
  (dk-have! hyp
    (lambda ()
      (dk-peel!)
      (dk-split-all!)
      (let ((i (cadr (cadr (dk-goal)))))
        (sml-nth-in-sab! i)
        (dk-lam-b!)
        (sab-directed! 'SENT `(NTH ,i l))
        (ass))))
  (sab-directed! 'RECEIVED '(LST l))                ; certifies DIRECTED(T) for the instantiation
  (let* ((ex (dk-cite! 'tuple-tabulation len aa f))
         (mm (dk-skolem! ex))
         (tab (dk-pick (lambda (f2) (and (dk-head-is? f2 'FORALL) (dk-contains? f2 mm) (dk-contains? f2 'VNB-LAMBDA)))
                       "the tabulated entries"))
         (x '(LIST RECEIVED (LST l)))
         (s `(CONS ,x ,mm)))
    (sab-directed! 'RECEIVED '(LST l))
    (sab-have-and! `(IN ,x ,aa) `(IN ,mm (TUPLES ,aa)))
    (fact 'cons-in-tuples aa x mm)
    (ew s)
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) 'IN)
            (begin (mac 'STRANDS) (ass))
            (begin
              (mac 'is-separate-trace)
              (ew 'l)
              (dk-conj-close!
                (lambda ()
                  (let ((g (dk-goal)))
                    (cond
                      ((dk-asm? g) (ass))
                      ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH))
                       (subst (dk-cite! 'length-cons x mm))
                       (subst `(= (LENGTH ,mm) ,len))
                       (rfl))
                      ((dk-head-is? g '=)
                       (fact 'nth-cons-1 x mm)
                       (ass))
                      (#t
                       (dk-peel!)
                       (let* ((g2 (dk-goal))                    ; (= (NTH (succ i) s) (LIST SENT (NTH i l)))
                              (i (cadr (cadr (cadr g2)))))
                         (sml-nth-in-sab! i)
                         (dk-have! `(<= ,i (LENGTH ,mm)) (lambda () (subst `(= (LENGTH ,mm) ,len)) (ass)))
                         (sab-have-and! `(IN ,i NN) `(<= 1 ,i) `(<= ,i (LENGTH ,mm)))
                         (fact 'nth-cons-succ i x mm)
                         (sab-have-and! `(IN ,i NN) `(<= 1 ,i) `(<= ,i ,len))
                         (dk-apply! tab i)
                         (subst `(= (NTH (succ ,i) ,s) (NTH ,i ,mm)))
                         (subst `(= (NTH ,i ,mm) (,f ,i)))
                         (sab-directed! 'SENT `(NTH ,i l))     ; certifies the list term for rfl
                         (if (not (dk-lam-b!)) (rfl))))))))))))))
(qed 'separate-trace-exists)

(sp (make-wff '(FORALL spa (FORALL l (IMPLIES (IN l (TUPLES (MSG-SET (TOKENS spa) (KEYS spa))))
   (FORSOME s (AND (IN s (STRANDS (TOKENS spa) (KEYS spa))) (IS-CONCAT-TRACE spa s))))))))
(dk-peel!)
(let* ((aa '(DIRECTED (TOKENS spa) (KEYS spa)))
       (len '(LENGTH l))
       (f `(VNB-LAMBDA cev_ NN (IF (<= cev_ ,len) (LIST RECEIVED (NTH cev_ l)) (LIST SENT (LST l)))))
       (hyp `(FORALL cei_ (IMPLIES (AND (IN cei_ NN) (AND (<= 1 cei_) (<= cei_ (succ ,len)))) (IN (,f cei_) ,aa)))))
  (fact 'length-in-nn '(MSG-SET (TOKENS spa) (KEYS spa)) 'l)
  (fact 'list-in-msgs '(TOKENS spa) '(KEYS spa) 'l)
  (fact 'nn-succ-closed len)
  (dk-have! hyp
    (lambda ()
      (dk-peel!)
      (dk-split-all!)
      (let ((i (cadr (cadr (dk-goal)))))
        (dk-lam-b!)
        (dk-case-if! (cadr (dk-goal))
          (lambda (true? v)
            (if true?
                (begin (sml-nth-in-sab! i) (sab-directed! 'RECEIVED `(NTH ,i l)) (ass))
                (begin (sab-directed! 'SENT '(LST l)) (ass))))))))
  (sab-directed! 'SENT '(LST l))                    ; certifies DIRECTED(T) for the instantiation
  (let* ((ex (dk-cite! 'tuple-tabulation `(succ ,len) aa f))
         (mm (dk-skolem! ex))
         (tab (dk-pick (lambda (f2) (and (dk-head-is? f2 'FORALL) (dk-contains? f2 mm) (dk-contains? f2 'VNB-LAMBDA)))
                       "the tabulated entries")))
    (ew mm)
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) 'IN)
            (begin (mac 'STRANDS) (ass))
            (begin
              (mac 'is-concat-trace)
              (ew 'l)
              (dk-conj-close!
                (lambda ()
                  (let ((g (dk-goal)))
                    (cond
                      ((dk-asm? g) (ass))
                      ((dk-head-is? g 'FORALL)                 ; the received entries
                       (dk-peel!)
                       (let ((i (cadr (cadr (dk-goal)))))
                         (dk-have! `(<= ,i (succ ,len)) (lambda () (dk-nn! `(<= ,i ,len))))
                         (sab-have-and! `(IN ,i NN) `(<= 1 ,i) `(<= ,i (succ ,len)))
                         (dk-apply! tab i)
                         (subst `(= (NTH ,i ,mm) (,f ,i)))
                         (dk-lam-b!)
                         (dk-if-branch! #t (cadr (dk-goal)) #f
                           (lambda () (sml-nth-in-sab! i) (sab-directed! 'RECEIVED `(NTH ,i l)) (rfl)))))
                      (#t                                      ; the sent entry, at succ(LENGTH l)
                       (dk-have! `(<= 1 (succ ,len)) (lambda () (dk-nn!)))
                       (dk-have! `(<= (succ ,len) (succ ,len)) (lambda () (dk-nn!)))
                       (sab-have-and! `(IN (succ ,len) NN) `(<= 1 (succ ,len)) `(<= (succ ,len) (succ ,len)))
                       (dk-apply! tab `(succ ,len))
                       (subst `(= (NTH (succ ,len) ,mm) (,f (succ ,len))))
                       (dk-lam-b!)
                       (dk-if-branch! #f (cadr (dk-goal))
                         (lambda () (fact 'nn-succ-not-le len) (ass))
                         (lambda () (sab-directed! 'SENT '(LST l)) (rfl))))))))))))))
(qed 'concat-trace-exists)

;;; The E and D traces of a key and a message are STRANDS of the space, and are what their
;;; predicates say (S-2b): the literal strands a protocol proof or an attack diagram writes down.
(define (sab-key-msg! k)                 ; k in KEYS(spa): land k as a message
  (dk-apply! (dk-cite! 'keys-in-tokens 'spa) k)
  (fact 'token-in-msgs '(TOKENS spa) '(KEYS spa) k))

(define (sab-strand-and-trace! lit pred ws)
  (let ((mem `(IN ,lit (STRANDS (TOKENS spa) (KEYS spa)))))
    (dk-have! mem (lambda () (mac 'STRANDS) (dk-each-leaf! (lambda () (ti)) (lambda () (ass)))))
    (dk-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal))
            (ass)
            (begin
              (mac pred)
              (let fill ((ws ws))
                (ew (car ws))
                (dk-conj-close!
                  (lambda ()
                    (cond ((dk-head-is? (dk-goal) 'FORSOME) (fill (cdr ws)))
                          ((dk-asm? (dk-goal)) (ass))
                          (#t (rfl))))))))))))

(sp (make-wff '(FORALL spa (FORALL k (FORALL m (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN k (KEYS spa))
  (IMPLIES (IN m (MSG-SET (TOKENS spa) (KEYS spa)))
    (AND (IN (LIST (LIST RECEIVED k) (LIST RECEIVED m) (LIST SENT (ENCR m k))) (STRANDS (TOKENS spa) (KEYS spa)))
         (IS-ENCRYPT-TRACE spa (LIST (LIST RECEIVED k) (LIST RECEIVED m) (LIST SENT (ENCR m k)))))))))))))
(dk-peel!)
(fact 'strand-space-parts 'spa)
(dk-split-all!)
(sab-key-msg! 'k)
(fact 'encr-in-msgs '(TOKENS spa) '(KEYS spa) 'm 'k)
(sab-directed! 'RECEIVED 'k)
(sab-directed! 'RECEIVED 'm)
(sab-directed! 'SENT '(ENCR m k))
(sab-strand-and-trace! '(LIST (LIST RECEIVED k) (LIST RECEIVED m) (LIST SENT (ENCR m k))) 'is-encrypt-trace '(k m))
(qed 'encrypt-trace-strand)

(sp (make-wff '(FORALL spa (FORALL k (FORALL m (IMPLIES (IS-STRAND-SPACE spa) (IMPLIES (IN k (KEYS spa))
  (IMPLIES (IN m (MSG-SET (TOKENS spa) (KEYS spa)))
    (AND (IN (LIST (LIST RECEIVED ((KINV spa) k)) (LIST RECEIVED (ENCR m k)) (LIST SENT m)) (STRANDS (TOKENS spa) (KEYS spa)))
         (IS-DECRYPT-TRACE spa (LIST (LIST RECEIVED ((KINV spa) k)) (LIST RECEIVED (ENCR m k)) (LIST SENT m))))))))))))
(dk-peel!)
(fact 'strand-space-parts 'spa)
(dk-split-all!)
(fact 'kinv-in-fun 'spa)
(sab-have-and! '(IN (KINV spa) (FUN (KEYS spa) (KEYS spa))) '(IN k (KEYS spa)))
(fact 'fun-apply-type '(KINV spa) '(KEYS spa) '(KEYS spa) 'k)
(sab-key-msg! '((KINV spa) k))
(fact 'encr-in-msgs '(TOKENS spa) '(KEYS spa) 'm 'k)
(sab-directed! 'RECEIVED '((KINV spa) k))
(sab-directed! 'RECEIVED '(ENCR m k))
(sab-directed! 'SENT 'm)
(sab-strand-and-trace! '(LIST (LIST RECEIVED ((KINV spa) k)) (LIST RECEIVED (ENCR m k)) (LIST SENT m)) 'is-decrypt-trace '(k m))
(qed 'decrypt-trace-strand)

(for-each (lambda (n) (topic! n 'constructions))
          '(encrypt-trace-no-origin decrypt-trace-no-origin encrypt-trace-strand decrypt-trace-strand sent-received-in-pair directed-intro separate-trace-exists concat-trace-exists nn-le-ne-succ text-trace-origin flush-trace-no-sent tee-trace-no-origin concat-trace-no-origin
            separate-trace-no-origin adversary-node-origin adversary-bound adversary-bound-adversary-nodes))
