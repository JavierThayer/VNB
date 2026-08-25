;;; theorem-library/subsequence-principle.scm
;;; ======================================================================
;;; subsequence-principle -- PROVEN.
;;;
;;;   In a metric space s, if EVERY subsequence of f has a further
;;;   subsequence converging to L, then f itself converges to L.
;;;
;;; This is the converse direction of `subseq-of-convergent'
;;; (theorem-library/subseq-convergence-proof): that one says convergence
;;; descends to every subsequence, this one says it can be recovered from
;;; the subsequences.  Together they are the standard tool for proving a
;;; sequence convergent when only subsequential information is available
;;; (uniqueness of subsequential limits, the usual route to "every
;;; subsequence has a convergent sub-subsequence with the same limit").
;;;
;;; ----------------------------------------------------------------------
;;; THE SHAPE OF THE STATEMENT, and why this one.
;;;
;;; The hypothesis is stated over REINDEXINGS, not over the predicate
;;; IS-SUBSEQUENCE:
;;;
;;;   forall phi. STRICTLY-MONO-NN(phi) =>
;;;      forsome psi. STRICTLY-MONO-NN(psi)
;;;                   and CONVERGES-TO(s, SUBSEQ(SUBSEQ(f,phi),psi), L)
;;;
;;; IS-SUBSEQUENCE(s,y,f) is `y = SUBSEQ(f,phi) for some strictly monotone
;;; phi', so the two readings are interchangeable -- but the predicate form
;;; would make the proof spend its first three steps unpacking an existential
;;; and an equation in order to recover exactly the phi the reindexing form
;;; hands over directly, and would make the CONSUMER assemble one to cite the
;;; theorem.  The nested SUBSEQ is likewise deliberate: it is the literal
;;; "subsequence of a subsequence", and SUBSEQ(SUBSEQ(f,phi),psi)(k) reduces to
;;; f(phi(psi(k))) in two `lam-b' steps (there is no composition operator on
;;; NN -> NN in the tree, and inventing one to state this theorem would put a
;;; new constructor between the statement and its meaning).
;;;
;;; The three typing hypotheses (IS-METRIC-SPACE, f in FUN(NN,PTS(s)),
;;; L in PTS(s)) are CHAINED implications, not one AND antecedent, so `fact'
;;; peels and detaches all of them in a single citation.
;;;
;;; ----------------------------------------------------------------------
;;; THE PROOF, and the one thing it deliberately does NOT do.
;;;
;;; The textbook argument is by contradiction: if f does not converge to L
;;; then some eps > 0 is missed infinitely often, those indices carry a
;;; subsequence staying eps away from L, and no further subsequence of THAT
;;; can converge to L.  Run literally, the first move is to push a negation
;;; through four quantifier alternations (NOT of the unfolded CONVERGES-TO),
;;; and VNB has no machinery for that: `prop' decides propositional
;;; entailment with every quantified formula an opaque atom, and there is no
;;; NNF/quantifier-negation tactic anywhere in the tree.  Done by hand it is
;;; three nested `pbc' + `have!' + `ai' sandwiches before the mathematics
;;; starts.  See the OBSTACLE note at the foot of this file.
;;;
;;; So the proof is arranged to be POSITIVE throughout.  Fix eps > 0 and put
;;;
;;;     S  =  { n in NN : not (d(f(n), L) <= eps) }
;;;
;;; and split on `CARD(S) in NN' -- a genuine case split, undecided by the
;;; context, and both branches are stated positively:
;;;
;;;   S FINITE.  nn-finite-subset-bounded gives a threshold N past which S
;;;     contains nothing, so for n >= N the index n is not in S, which
;;;     (one `sep-mi' under a `pbc') is d(f(n),L) <= eps.  That IS the
;;;     convergence estimate at eps; N is the witness.
;;;
;;;   S INFINITE.  S is then in INF-SUBSETS(NN), so subsequence-capture
;;;     yields a strictly monotone enumeration g : NN -> S.  The hypothesis
;;;     applied to g yields psi with SUBSEQ(SUBSEQ(f,g),psi) -> L, hence an
;;;     index K with d(SUBSEQ(SUBSEQ(f,g),psi)(K), L) <= eps; that term
;;;     reduces to f(g(psi(K))), and g(psi(K)) lies in S, i.e. the distance
;;;     is NOT <= eps.  Contradiction, so this branch is vacuous.
;;;
;;; Only the eps-branch of CONVERGES-TO needs the hypothesis at all; the
;;; three definitional conjuncts come straight from the premises.
;;;
;;; ----------------------------------------------------------------------
;;; WHAT THIS FILE ADDS
;;;
;;;   fun-codomain-subset      PROVEN here (modulo 0), from fun-codomain-iff
;;;                            + subset-def.  Widening the codomain of a
;;;                            function along a subset inclusion had no
;;;                            statement in the tree; it is needed the moment
;;;                            subsequence-capture's g : NN -> S has to be
;;;                            read as an element of FUN(NN,NN), which is what
;;;                            STRICTLY-MONO-NN demands.  Generic, reusable.
;;;
;;;   nn-finite-subset-bounded ASSERTED, warrant `well-known'.  A finite
;;;                            subset of NN is bounded.  This is the exact
;;;                            CONVERSE of `inf-subset-nn-unbounded'
;;;                            (diagonalization-lemmas.scm, itself asserted
;;;                            well-known) and neither direction was in the
;;;                            tree in this direction.  See its warrant.
;;;
;;; Dependencies: cauchy-subsequence (STRICTLY-MONO-NN, SUBSEQ),
;;; subsequence-capture, inf-subsets, metric-completeness (CONVERGES-TO),
;;; fun-apply-type-proof (fun-apply-type-c), interactive/proof-debt,
;;; driver-kit (have!, use-em, the dk- kit).  Loads beside
;;; subseq-convergence-proof.
;;; ======================================================================

;;; -----------------------------------------------------------------------
;;; fun-codomain-subset -- widen the codomain along a subset inclusion.
;;;
;;;     f in FUN(A,B)  and  B subset C   =>   f in FUN(A,C)
;;;
;;; Curried, so `fact' detaches both hypotheses in one call.  The proof is
;;; fun-codomain-iff in both directions with subset-def in between: the
;;; domain conjunct transfers verbatim, and the value conjunct is one
;;; instantiation of each.
(sp (make-wff '(FORALL g_ (FORALL a_ (FORALL b_ (FORALL c_
   (IMPLIES (IN g_ (FUN a_ b_))
     (IMPLIES (SUBSET b_ c_)
       (IN g_ (FUN a_ c_))))))))))
(quietly (lambda ()
  (dk-peel-to! 'IN)
  (mac 'fun-codomain-iff)
  (mac-h 'fun-codomain-iff '(IN g_ (FUN a_ b_)))
  (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
  (let* ((bs  (dk-opened (lambda () (di))))
         (dom (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'IN)) bs))
         (val (any-pred (lambda (n) (not (eq? n dom))) bs)))
    (dk-focus! dom) (ass)
    (dk-focus! val) (di)
    (let ((x (cadr (cadr (dk-goal)))))
      (inst+ (any-pred (dk-head? 'FORALL) (dk-asms)) x)
      (mac-h 'subset-def '(SUBSET b_ c_))
      (inst+ (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                        (eq? (car (caddr a)) 'IMPLIES)
                                        (equal? (caddr (cadr (caddr a))) 'b_)))
                       (dk-asms))
             (list 'g_ x))
      (ass)))))
(qed 'fun-codomain-subset)
(topic! 'fun-codomain-subset 'plumbing)

;;; -----------------------------------------------------------------------
;;; nn-finite-subset-bounded -- a FINITE subset of NN is bounded.
;;;
;;; Stated in the form the analysis consumes: there is a threshold N past
;;; which T contains nothing.  (The equivalent "every y in T satisfies
;;; y < N" would force every consumer to turn `N <= y' plus `y < N' into a
;;; contradiction by hand, i.e. to reach for the arithmetic oracle at a leaf
;;; where the mathematics is purely set-theoretic.)
;;;
;;; This is the exact converse of `inf-subset-nn-unbounded'
;;; (theorem-library/diagonalization-lemmas.scm), which says an INFINITE
;;; subset of NN is unbounded and is itself asserted `well-known'.  The tree
;;; had one direction and not the other.
(support 'nn-finite-subset-bounded
  '(FORALL T
     (IMPLIES (SUBSET T NN)
       (IMPLIES (IN (CARD T) NN)
         (FORSOME N (AND (IN N NN)
                         (FORALL y (IMPLIES (IN y NN)
                                     (IMPLIES (<= N y) (NOT (IN y T)))))))))))
(warrant! 'nn-finite-subset-bounded 'well-known
  "A finite subset T of NN is bounded.  By finite-set-induction (cardinality.scm,
   primitive) on T: the empty set is bounded by N = 0, and if T is bounded by N
   then T u {x} is bounded by max(succ x, N) (nn-pair-upper-bound, order-lemmas).
   Hence some N in NN has y < N for every y in T, so no y >= N is in T.  The
   contrapositive of `inf-subset-nn-unbounded' (diagonalization-lemmas.scm),
   which asserts the same equivalence from the other side and is warranted the
   same way.  Not mechanised: the induction runs over a COMP class
   { T | T subset NN => bounded } and wants the comprehension-membership
   bookkeeping, sethood of T, and the max-of-two-naturals brick threaded through
   -- routine, and no library payoff beyond this one citation.")
(topic! 'nn-finite-subset-bounded 'combinatorial)

;;; -----------------------------------------------------------------------
;;; The theorem.
;;;
;;; file-local helpers, `ssp-' prefix throughout: nothing here may be named
;;; like a tactic or a registered constant (the reader case-folds).

;;; Split the unfolded CONVERGES-TO conjunction, closing every conjunct that
;;; is already a context assumption, and land on the eps-universal.  Never
;;; counts `di's: it loops on the goal's HEAD and errors if it runs away.
(define (ssp-defsplit!)
  (let loop ((k 0))
    (if (> k 6) (error "ssp-defsplit!: runaway"))
    (if (eq? (car (dk-goal)) 'and)
        (let* ((bs   (dk-opened (lambda () (di))))
               (rest (any-pred (lambda (n) (memq (car (dk-goal-of n)) '(and forall))) bs))
               (easy (any-pred (lambda (n) (not (eq? n rest))) bs)))
          (dk-focus! easy) (ass)
          (dk-focus! rest) (loop (+ k 1)))
        'done)))

(sp (make-wff
  '(FORALL s (FORALL f (FORALL l
     (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (IN f (FUN NN (PTS s)))
     (IMPLIES (IN l (PTS s))
     (IMPLIES (FORALL phi (IMPLIES (STRICTLY-MONO-NN phi)
                 (FORSOME psi (AND (STRICTLY-MONO-NN psi)
                                   (CONVERGES-TO s (SUBSEQ (SUBSEQ f phi) psi) l)))))
       (CONVERGES-TO s f l))))))))))

(quietly (lambda ()
  (dk-peel-to! 'CONVERGES-TO)
  (mac 'CONVERGES-TO)
  (ssp-defsplit!)
  (di)                                  ; eps
  (di)))                                ; pos-rr(eps)

;; The hypothesis and the eps in hand; S is the set of indices where f is
;; further than eps from l.  Read eps off the CONTEXT, never off a guess.
(define ssp-hyp (any-pred (dk-head? 'FORALL) (dk-asms)))
(define ssp-eps (cadr (any-pred (dk-head? 'POS-RR) (dk-asms))))
(define ssp-set `(SEP n0_ NN (NOT (<= ((DIST s) (f n0_) l) ,ssp-eps))))

(quietly (lambda ()
  (have! `(SUBSET ,ssp-set NN)
         (lambda () (mac 'subset-def) (di)
                    (sep-me (any-pred (dk-head? 'IN) (dk-asms)))
                    (ass)))))

;;; ---- S FINITE: the threshold is the convergence witness -----------------
(define (ssp-finite!)
  (let* ((ex     (dk-fact! 'nn-finite-subset-bounded ssp-set))
         (landed (dk-landed (lambda () (ai ex))))
         (two    (dk-split! (any-pred (dk-head? 'AND) landed)))
         (miss   (any-pred (dk-head? 'FORALL) two))
         (thr    (cadr (any-pred (dk-head? 'IN) two))))
    (dk-ew-split! thr (lambda () (ass))
      (lambda ()
        (di) (di) (di)                          ; n_, (in n_ nn), (<= thr n_)
        (let* ((idx (cadr (cadr (cadr (dk-goal)))))
               (neg (dk-deepest (lambda () (inst+ miss idx)))))   ; not (in n_ S)
          (pbc)                                 ; assume not(d <= eps); goal FALSITY
          (have! `(IN ,idx ,ssp-set)
                 (lambda ()
                   (for-each (lambda (n) (dk-focus! n) (ass))
                             (dk-opened (lambda () (sep-mi))))))
          (ai neg))))))

;;; ---- S INFINITE: capture it, and the hypothesis refutes the branch ------
(define (ssp-infinite!)
  (have! `(IN ,ssp-set (INF-SUBSETS NN))
         (lambda () (mac 'inf-subsets-membership) (from-context!)))
  (let* ((ex     (dk-fact! 'subsequence-capture ssp-set))
         (landed (dk-landed (lambda () (ai ex))))
         (two    (dk-split! (any-pred (dk-head? 'AND) landed)))
         (enum   (cadr (any-pred (dk-head? 'IN) two))))     ; g : NN -> S
    (dk-fact! 'fun-codomain-subset enum 'NN ssp-set 'NN)
    (have! `(STRICTLY-MONO-NN ,enum)
           (lambda () (mac 'STRICTLY-MONO-NN) (from-context!)))
    ;; the hypothesis at g: a further subsequence that converges
    (let* ((ex2  (dk-deepest (lambda () (inst+ ssp-hyp enum))))
           (two2 (dk-split! (any-pred (dk-head? 'AND)
                                      (dk-landed (lambda () (ai ex2))))))
           (conv (any-pred (dk-head? 'CONVERGES-TO) two2))
           (psi  (caddr (caddr conv))))
      (mac-h 'CONVERGES-TO conv)
      (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
      (let* ((epsu (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                              (eq? (cadr a) 'eps)))
                             (dk-asms)))
             (ex3  (dk-deepest (lambda () (inst+ epsu ssp-eps))))
             (two3 (dk-split! (any-pred (dk-head? 'AND)
                                        (dk-landed (lambda () (ai ex3))))))
             (thr  (cadr (any-pred (dk-head? 'IN) two3)))
             (tail (any-pred (dk-head? 'FORALL) two3)))
        ;; the estimate AT the threshold itself
        (dk-fact! 'nn-le-refl thr)
        (dk-deepest (lambda () (inst+ tail thr)))
        ;; ... and that same term is a term of the CAPTURED subsequence, so it
        ;; is more than eps from l.
        (have! `(IN ,psi (FUN NN NN))
               (lambda () (mac-h 'STRICTLY-MONO-NN `(STRICTLY-MONO-NN ,psi))
                          (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
                          (ass)))
        (dk-fact! 'fun-apply-type-c psi 'NN 'NN thr)
        (dk-fact! 'fun-apply-type-c enum 'NN ssp-set `(,psi ,thr))
        (let* ((mem `(IN (,enum (,psi ,thr)) ,ssp-set))
               (neg (any-pred (dk-head? 'NOT) (dk-landed (lambda () (sep-me mem)))))
               (trm `(f (,enum (,psi ,thr))))
               (sub `(SUBSEQ (SUBSEQ f ,enum) ,psi)))
          ;; SUBSEQ(SUBSEQ(f,g),psi)(K) == f(g(psi(K))): two unfolds, two betas.
          (have! `(== ,trm (,sub ,thr))
                 (lambda () (mac 'SUBSEQ) (lam-b) (mac 'SUBSEQ) (lam-b) (qrfl)))
          (have! `(<= ((DIST s) ,trm l) ,ssp-eps)
                 (lambda () (subst `(== ,trm (,sub ,thr))) (ass)))
          (ai neg))))))

(quietly (lambda ()
  (use-em `(IN (CARD ,ssp-set) NN) ssp-finite! ssp-infinite!)))

(if (proof-done? *ps*)
    (qed 'subsequence-principle)
    (error "subsequence-principle: proof did not complete"))
(topic! 'subsequence-principle 'analysis)

;;; ======================================================================
;;; OBSTACLE RECORDED (2026-08-19): there is no quantifier-negation move.
;;;
;;; The proof above is arranged around a gap rather than through it.  The
;;; direct argument -- "suppose f does not converge to L" -- needs
;;;
;;;     NOT CONVERGES-TO(s,f,L)
;;;       |-  forsome eps. POS-RR(eps) and
;;;             forall n in NN. forsome n_ in NN. n <= n_ and
;;;                             NOT (d(f(n_),L) <= eps)
;;;
;;; which is four alternations of classical negation-pushing.  Nothing in the
;;; tree does it: `prop' (prop.scm) is propositional and treats every FORALL /
;;; FORSOME as an opaque atom, `contra' is arithmetic, and grep finds no NNF,
;;; no `not-forall', no `not-forsome'.  By hand each alternation costs a `pbc',
;;; a `have!' of the positive with an `ew'/`di' lane inside it, and an `ai' --
;;; three nested sandwiches, roughly forty lines, before any mathematics
;;; happens, and every line of it generic.
;;;
;;; The mechanism that would dissolve the class -- and it IS a class; the same
;;; move opens every "suppose the sequence does NOT converge / the set is NOT
;;; bounded / the function is NOT continuous" argument in analysis -- is a
;;; tactic in the shape of `prop':
;;;
;;;     (nnf-h FORM)   rewrite a NOT-headed hypothesis into negation normal
;;;                    form, pushing NOT through FORALL/FORSOME/AND/OR/IMPLIES
;;;                    and discharging each step through the kernel rules the
;;;                    way `prop' discharges its decision, so it adds no trust.
;;;
;;; It is the natural companion to `prop' and `contra' -- the third member of
;;; the "obvious leaf that wants a bespoke dance" family named in CLAUDE.md --
;;; and it is what a user typing `what-now' at a NOT-headed hypothesis should
;;; be offered.
;;; ======================================================================
