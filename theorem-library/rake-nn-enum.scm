;;; theorem-library/rake-nn-enum.scm
;;; ====================================================================
;;; The chosen enumeration NN-ENUM and the two strictly-monotone bricks the
;;; refinement tower (convergence-block-tower) wants.
;;;
;;;   nn-enum-spec                  (support, subsequence-capture.scm:37)
;;;   strictly-mono-image-infinite  (new brick)
;;;   strictly-mono-le-reflect      (new brick)
;;;
;;; L1.  nn-enum-spec.  NN-ENUM(S) is CHOICE over
;;;        SEP f (FUN NN S) . f strictly monotone,
;;;      and subsequence-capture -- PROVEN since 2026-09-19
;;;      (theorem-library/rake-subseq-leaves.scm) -- is exactly the statement
;;;      that this SEP is INHABITED.  So the proof is `mac' the functoid in the
;;;      goal, `choose!' the SEP with the captured f as the witness, and read
;;;      the two conjuncts off the landed SEP membership.  The SEP is read OFF
;;;      THE REWRITTEN GOAL, never rebuilt, so this file cannot drift from what
;;;      def-functoid installed.
;;;
;;; L2.  strictly-mono-image-infinite.  For psi strictly monotone with all its
;;;      values in A subset NN, the set of values
;;;        { m in A : some k in NN has m = psi(k) }
;;;      is an INFINITE subset of NN.  Infinitude needs no CARD arithmetic:
;;;      split on (IN (CARD J) NN) -- here by NOT-introduction, the goal after
;;;      `mac inf-subsets-membership' being literally that negation -- and
;;;      refute the finite side with nn-finite-subset-bounded (a threshold N
;;;      past which nothing is in J) against psi(N) >= N (strictly-mono-ge-id).
;;;      psi(N) is in J and is at least N: contradiction.  The pattern is
;;;      theorem-library/subsequence-principle.scm:200-220.
;;;      The SEP is taken over A rather than over NN so that "J subset A" is a
;;;      one-line consequence at the call site (the tower wants J subset the
;;;      block it refines).
;;;
;;; L3.  strictly-mono-le-reflect.  psi(i) <= psi(j) => i <= j.  Case split on
;;;      (< j i): on the negative side nn-not-lt-le IS the goal; on the positive
;;;      side monotonicity gives psi(j) < psi(i), nn-lt-succ-le turns that into
;;;      succ(psi j) <= psi i and nn-succ-le-antisym into NOT (psi i <= psi j),
;;;      which contradicts the hypothesis.
;;;
;;; DEFINEDNESS (the LUTINS rule).  Every term instantiated at here is typed
;;; first: psi(N) by fun-apply-type-c off the FUN NN NN read out of
;;; STRICTLY-MONO-NN, the SEP by its own (certified) domain, and the `rfl' that
;;; closes (= psi(N) psi(N)) runs with (IN (psi N) NN) already in context.
;;;
;;; LOAD WINDOW [306, 455).
;;;   lo = 306: the latest citation is `subsequence-capture', proven in
;;;   theorem-library/rake-subseq-leaves (position 305).  The others:
;;;   nn-finite-subset-bounded (273), strictly-mono-ge-id (rake-algebra, 234),
;;;   nn-succ-le-antisym (nn-order-via-rr, 227), nn-lt-succ-le (finite-surgery,
;;;   224), subset-mem (subset-lemmas, 191), nn-not-lt-le (nn-not-lt-le-proof,
;;;   171), fun-apply-type-c (fun-apply-type-proof, 160), STRICTLY-MONO-NN
;;;   (cauchy-subsequence, 90), NN-ENUM + the retired support
;;;   (subsequence-capture, 89), inf-subsets-membership
;;;   (structure-library/inf-subsets, 85), number-systems (34), choice-axiom
;;;   (theory, 11).
;;;   hi = 455: NO proof in the tree cites nn-enum-spec today (it is named only
;;;   in comments, in founder-warrants.scm:94 -- a SECOND warrant!, which must
;;;   be retired with the support -- and in pss-topics.scm:199), but all three
;;;   theorems here are cited by theorem-library/rake-block-tower.scm of the
;;;   same batch, whose own window is [454, 465).  So this file goes anywhere
;;;   in [306, 455) and the tower immediately after it.
;;;
;;; Helper prefix: r8l-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r8l-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-nn-enum: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-nn-enum: unfinished" name))))

;; (IN t (SEP ...)) closed by `ass' on BOTH halves, whichever way sep-mi
;; decides to ground them.  `in-sep!' demands exactly two open leaves and errors
;; when the domain half is already in the context and sep-mi grounds it on the
;; spot (the note in rake-dc-on-nn.scm's relation lane).
(define (r8l-in-sep-by-ass!)
  (for-each (lambda (l) (dk-focus! l) (ass))
            (dk-opened (lambda () (sep-mi)))))

;; The FUN NN NN typing carried by STRICTLY-MONO-NN, landed on the MAIN branch
;; without consuming the predicate: `mac-h' REPLACES what it unfolds, so the
;; unfold is done inside a `have!' lane and only the typing crosses back.
(define (r8l-fun-typing! ps)
  (have! (list 'IN ps '(FUN NN NN))
    (lambda ()
      (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN ps))
      (dk-split-all!)
      (ass))))

;;; =====================================================================
;;; L1.  nn-enum-spec -- THE SUPPORT, stated literally
;;; (theorem-library/subsequence-capture.scm:37).
;;; =====================================================================

(sp (make-wff
  '(FORALL S
     (IMPLIES (IN S (INF-SUBSETS NN))
       (AND (IN (NN-ENUM S) (FUN NN S))
            (FORALL m
              (IMPLIES (IN m NN)
                (FORALL n
                  (IMPLIES (IN n NN)
                    (IMPLIES (< m n)
                             (< ((NN-ENUM S) m)
                                ((NN-ENUM S) n))))))))))))

(dk-peel!)

(define r8l-e-S
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) '(INF-SUBSETS NN))))
                 "the INF-SUBSETS typing of S")))

;; Unfold the functoid IN THE GOAL; the CHOICE and its SEP are then read off
;; what the macete produced.
(mac 'NN-ENUM)

(define r8l-e-choice (cadr (cadr (dk-goal))))    ; (CHOICE (SEP f (FUN NN S) ...))
(if (not (and (pair? r8l-e-choice) (eq? (car r8l-e-choice) 'CHOICE)))
    (error "rake-nn-enum: mac 'NN-ENUM left no CHOICE in the goal"
           (expression->string (dk-goal))))
(define r8l-e-sep (cadr r8l-e-choice))

;; subsequence-capture makes that SEP inhabited.
(let* ((ex (dk-fact! 'subsequence-capture r8l-e-S))
       (w  (dk-skolem! ex)))                    ; (IN w (FUN NN S)) + monotonicity
  (choose! r8l-e-sep w (lambda () (r8l-in-sep-by-ass!))))

(dk-conj-close! (lambda () (ass)))

(r8l-qed! 'nn-enum-spec)
;; topic! for this name is set in theorem-library/pss-topics.scm:199 -- not repeated here.

;;; =====================================================================
;;; L2.  strictly-mono-image-infinite.
;;; =====================================================================

(sp (make-wff
  '(FORALL psi
     (IMPLIES (STRICTLY-MONO-NN psi)
       (FORALL A
         (IMPLIES (SUBSET A NN)
           (IMPLIES (FORALL k_ (IMPLIES (IN k_ NN) (IN (psi k_) A)))
             (IN (SEP m_ A (FORSOME j_ (AND (IN j_ NN) (= m_ (psi j_)))))
                 (INF-SUBSETS NN)))))))))

(define r8l-i-landed (dk-peel!))

(define r8l-i-psi
  (cadr (dk-pick (dk-head? 'STRICTLY-MONO-NN) "the monotonicity hypothesis")))
(define r8l-i-A
  (cadr (dk-pick (dk-head? 'SUBSET) "the ambient subset typing")))
(define r8l-i-ptw
  (or (any-pred (dk-head? 'FORALL) r8l-i-landed)
      (error "strictly-mono-image-infinite: no pointwise typing hypothesis")))
(define r8l-i-J (cadr (dk-goal)))                ; the SEP, READ OFF the goal

(r8l-fun-typing! r8l-i-psi)

;; J subset NN: an element of J is an element of A, and A subset NN.
(have! (list 'SUBSET r8l-i-J 'NN)
  (lambda ()
    (mac 'subset-def)
    (let ((xv (dk-di-var!)))
      (sep-me (list 'IN xv r8l-i-J))
      (fact 'subset-mem-fwd r8l-i-A 'NN xv)
      (ass))))

(mac 'inf-subsets-membership)

(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (eq? (car g) 'SUBSET)
         (ass)
         ;; (NOT (IN (CARD J) NN)) -- assume it and refute.
         (begin
           (di)                                  ; (IN (CARD J) NN); goal FALSITY
           (let* ((ex   (dk-fact! 'nn-finite-subset-bounded r8l-i-J))
                  (bigN (dk-skolem! ex))
                  (miss (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                  (dk-contains? f r8l-i-J)))
                                 "the past-the-threshold miss")))
             (fact 'strictly-mono-ge-id r8l-i-psi bigN)        ; bigN <= psi(bigN)
             (fact 'fun-apply-type-c r8l-i-psi 'NN 'NN bigN)   ; psi(bigN) in NN
             (let ((neg (dk-apply! miss (list r8l-i-psi bigN))))   ; NOT (psi bigN in J)
               (have! (list 'IN (list r8l-i-psi bigN) r8l-i-J)
                 (lambda ()
                   (in-sep!
                    (lambda () (dk-apply! r8l-i-ptw bigN) (ass))
                    (lambda ()
                      (witness! bigN
                        (lambda ()
                          (dk-conj-close!
                           (lambda ()
                             (if (eq? (car (dk-goal)) 'IN) (ass) (rfl))))))))))
               (ai neg))))))))

(r8l-qed! 'strictly-mono-image-infinite)
(gloss! 'strictly-mono-image-infinite
  "The set of values of a strictly monotone psi : NN -> NN, separated inside any
   subset A of NN that contains them all, is an infinite subset of NN.  The
   brick behind 'the block refined by a subsequence is still infinite'.")
(topic! 'strictly-mono-image-infinite 'combinatorial)

;;; =====================================================================
;;; L3.  strictly-mono-le-reflect -- order reflection.
;;; =====================================================================

(sp (make-wff
  '(FORALL psi
     (IMPLIES (STRICTLY-MONO-NN psi)
       (FORALL i_
         (IMPLIES (IN i_ NN)
           (FORALL j_
             (IMPLIES (IN j_ NN)
               (IMPLIES (<= (psi i_) (psi j_)) (<= i_ j_))))))))))

(define r8l-r-landed (dk-peel!))

(define r8l-r-psi
  (cadr (dk-pick (dk-head? 'STRICTLY-MONO-NN) "the monotonicity hypothesis")))
(define r8l-r-i (cadr (dk-goal)))
(define r8l-r-j (caddr (dk-goal)))

;; STRICTLY-MONO-NN is not needed intact afterwards, so it is unfolded on the
;; main branch and both conjuncts kept.
(define r8l-r-mono
  (let ((atoms (begin (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN r8l-r-psi))
                      (dk-split-all!))))
    (or (any-pred (dk-head? 'FORALL) atoms)
        (error "strictly-mono-le-reflect: no monotonicity universal in the split"))))

(fact 'fun-apply-type-c r8l-r-psi 'NN 'NN r8l-r-i)
(fact 'fun-apply-type-c r8l-r-psi 'NN 'NN r8l-r-j)

(use-em (list '< r8l-r-j r8l-r-i)
  (lambda ()                                   ; j < i: monotonicity refutes
    (dk-apply! r8l-r-mono r8l-r-j r8l-r-i)     ; psi(j) < psi(i)
    (fact 'nn-lt-succ-le (list r8l-r-psi r8l-r-j) (list r8l-r-psi r8l-r-i))
    (fact 'nn-succ-le-antisym (list r8l-r-psi r8l-r-j) (list r8l-r-psi r8l-r-i))
    (pbc)
    (ai (list 'NOT (list '<= (list r8l-r-psi r8l-r-i) (list r8l-r-psi r8l-r-j)))))
  (lambda ()                                   ; NOT (j < i): nn-not-lt-le IS the goal
    (fact 'nn-not-lt-le r8l-r-j r8l-r-i)
    (ass)))

(r8l-qed! 'strictly-mono-le-reflect)
(gloss! 'strictly-mono-le-reflect
  "A strictly monotone psi : NN -> NN reflects the order: psi(i) <= psi(j)
   implies i <= j.  The converse direction of the monotonicity clause, needed
   whenever an index is recovered from its image under an enumeration.")
(topic! 'strictly-mono-le-reflect 'inequalities)
