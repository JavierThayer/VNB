;;; nn-pairing.scm -- the Cantor pairing NN x NN -> NN, and the arithmetic it
;;; needs.  Step one of the missing re-indexing mechanism.
;;;
;;; WHY THIS FILE EXISTS.  Several developments are blocked on one absent fact:
;;; a surjection NN -> NN x NN, equivalently the ability to re-index a doubly
;;; indexed family by a single natural.  `compact-metric-is-separable'
;;; (structure-library/separable.scm) needs it to enumerate the union of the
;;; finite (1/(n+1))-nets as one sequence; `coordinatewise-diagonal-subseq'
;;; (theorem-library/ascoli-arzela-statement.scm) and the countable unions of
;;; structure-library/sigma-algebra.scm want the same thing.  Selecting the nets
;;; and enumerating each one were never the obstacle -- CHOICE and FIN-ENUM
;;; (structure-library/finsum.scm) already do that.  Only the re-indexing was.
;;;
;;; THE CONSTRUCTION.  Cantor's pairing, but with the triangular numbers defined
;;; by RECURSION rather than by the closed form s(s+1)/2:
;;;
;;;   TRINUM(0) = 0,   TRINUM(succ n) = TRINUM(n) + succ n
;;;   NNPAIR(i, j) = TRINUM(i + j) + j
;;;
;;; The closed form would drag in division and the proof that s(s+1) is even;
;;; the recursion needs neither.  The alternative route -- a staircase walk
;;; W(succ n) = if fst > 0 then (fst-1, snd+1) else (snd+1, 0) -- was rejected
;;; because every step of its surjectivity proof must resolve an IF guard and a
;;; predecessor, where Cantor's obligations are plain equational arithmetic.
;;;
;;; WHAT IS PROVED HERE.  Both halves of the bijection: `nnpair-onto' is
;;; surjectivity, which makes the projections TOTAL, and `nnpair-inj' (added
;;; 2026-07-31) is injectivity, which makes them WELL DEFINED.  `trinum-mono'
;;; and `nnpair-diag-bound' / `nnpair-cross' are the order rungs injectivity
;;; stands on -- the last says a code on antidiagonal s is strictly below every
;;; code on a later antidiagonal, which is the whole geometric content.
;;; The projections NNFST / NNSND are here too, as definite descriptions, and
;;; `nn-flatten' -- the fact everything downstream consumes -- completes the
;;; mechanism.  See the note at the foot of this file.
;;;
;;; Loads after nn-parity-proof (nn-zero-or-succ, the i = 0 / i = succ q split),
;;; structure-library/ordinals (def-by-nn-recursion) and number-systems (NN, +,
;;; succ, and the addition axioms).  Binders carry the trailing underscore that
;;; the case-fold convention wants.
;;; ====================================================================

;;; ---- the definitions ---------------------------------------------------

;;; TRINUM(n) = 0 + 1 + ... + n.  def-by-nn-recursion installs trinum-zero and
;;; trinum-succ as quasi-equalities, stamped `definitional'.
(def-by-nn-recursion 'TRINUM '() '0 '(n_ val_) '(+ val_ (succ n_)))

;;; NNPAIR(i, j) = TRINUM(i + j) + j -- the position of (i, j) when NN x NN is
;;; enumerated one antidiagonal at a time, j steps along the antidiagonal i + j.
(def-functoid 'NNPAIR '(i_ j_) '(+ (TRINUM (+ i_ j_)) j_))

(notation! 'TRINUM 'kind 'functoid 'arity 1
           'english "the $1-th triangular number")
(notation! 'NNPAIR 'kind 'functoid 'arity 2
           'english "the Cantor code of ($1, $2)")

;;; ---- file-local helpers -----------------------------------------------
;;; Navigation (dk-focus-goal! / dk-focus-ctx! / dk-ai-head! / dk-peel-to! /
;;; dk-ew-split!) now lives in driver-kit.scm, promoted there when
;;; nn-order-proof needed the same helpers.  What stays here is the other kind:
;;; each of these exists ONLY because a tactic is weak, and each should
;;; disappear when the tactic is fixed rather than be promoted anywhere.

;;; nn-add-comm and nn-add-closed each have ONE conjunctive antecedent, which
;;; `fact' will not cross -- so establish the AND first.  (from-context! in
;;; driver-kit already special-cases (IN a*b NN) via nn-mul-closed and has no
;;; case for (IN a+b NN); adding one would delete np2-sum-type! outright.)
(define (np2-comm! x y)
  (have! `(AND (IN ,x NN) (IN ,y NN)))
  (fact 'nn-add-comm x y))
(define (np2-sum-type! x y)
  (have! `(AND (IN ,x NN) (IN ,y NN)))
  (fact 'nn-add-closed x y))

;;; rfl's definedness guard: (= t t) is the DEFINEDNESS assertion for t under
;;; VNB's partial equality, so a syntactically reflexive goal still needs the
;;; context to know t is defined.  Land the typing first.
(define (np2-defined-succ-sum! x y)
  (np2-sum-type! x y)
  (fact 'nn-succ-closed `(+ ,x ,y)))

;;; ---- trinum-type : TRINUM(n) in NN -------------------------------------
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (IN (TRINUM n_) NN)))))
(ni)
(dk-focus-goal! "trinum(0)")
(mac 'trinum-zero)
(fact 'nn-zero-in)
(ass)
(dk-focus-goal! "implies")
(di) (di)
(mac 'trinum-succ)
(fact 'nn-succ-closed 'n_)
(have! '(AND (IN (TRINUM n_) NN) (IN (succ n_) NN)))
(fact 'nn-add-closed '(TRINUM n_) '(succ n_))
(ass)
(qed 'trinum-type)

;;; ---- trinum-mono : a <= b => TRINUM(a) <= TRINUM(b) --------------------
;;; Induction on b.  Base: a <= 0 forces a = 0.  Step: a <= succ b splits into
;;; a <= b, where the IH plus TRINUM(b) <= TRINUM(b) + succ b = TRINUM(succ b)
;;; does it, and a = succ b, where the two sides coincide.  This is the half of
;;; the injectivity argument that says a smaller antidiagonal starts lower.
(sp (make-wff '(FORALL b_ (IMPLIES (IN b_ NN)
                 (FORALL a_ (IMPLIES (IN a_ NN)
                   (IMPLIES (<= a_ b_) (<= (TRINUM a_) (TRINUM b_)))))))))
(ni)
(dk-focus-goal! "trinum(0)")
(dk-peel-to! '<=)
(fact 'nn-le-zero-is-zero 'a_)
(subst '(= a_ 0))
(fact 'trinum-type 0)
(fact 'nn-le-refl '(TRINUM 0))
(ass)
(dk-focus-goal! "succ(b_)")
(di) (di)
(let ((ih (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL))) (dk-asms))
              (error "trinum-mono: no IH"))))
  (dk-peel-to! '<=)
  (fact 'nn-le-succ-cases 'b_ 'a_)
  (for-each
    (lambda (br)
      (dk-focus! br)
      (if (any-pred (lambda (a) (equal? a '(<= a_ b_)))
                    (map wff-formula (sequent-node-assumptions br)))
          (begin
            (inst+ ih 'a_)
            (mac 'trinum-succ)
            (fact 'trinum-type 'b_)
            (fact 'nn-succ-closed 'b_)
            ;; nn-le-add-right binds the ADDEND outermost: (fact 'nn-le-add-right X Y) is
            ;; Y <= Y + X, so the successor goes first.
            (fact 'nn-le-add-right '(succ b_) '(TRINUM b_))
            ;; nn-le-trans became GUARDED on NN (2026-08-02), so every term it
            ;; chains through must be typed -- this site was chaining through
            ;; TRINUM(b_) + succ(b_) without ever saying it was a natural.
            (fact 'trinum-type 'a_)
            (np2-sum-type! '(TRINUM b_) '(succ b_))
            (fact 'nn-le-trans-guarded '(TRINUM a_) '(TRINUM b_) '(+ (TRINUM b_) (succ b_)))
            (ass))
          (begin
            (subst '(= a_ (succ b_)))
            (fact 'nn-succ-closed 'b_)
            (fact 'trinum-type '(succ b_))
            (fact 'nn-le-refl '(TRINUM (succ b_)))
            (ass))))
    (dk-opened (lambda () (dk-ai-head! 'OR)))))
(qed 'trinum-mono)

;;; ---- succ(a) + b = succ(a + b) -- now cited as `tab-succ-add' ----------
;;; The base has nn-add-succ (a + succ b = succ(a + b)) and nothing for a succ
;;; on the LEFT, which the pairing step needs in order to recognise
;;; succ(q) + j as succ(q + j).  It was proved here as `nn-succ-add'; REMOVED
;;; 2026-09-20 (batch 11, proven-duplicate-audit): it was alpha-equal to
;;; `tab-succ-add' (theorem-library/tuple-tabulation.scm:344), which loads
;;; before this file and uses its own copy five times, so that is the name
;;; that had to survive.  The citation below names it.

;;; ---- nnpair-onto : every natural is a Cantor code ----------------------
;;; forall n in NN, forsome i, j in NN.  NNPAIR(i, j) = n.
;;;
;;; Induction on n.  Base: NNPAIR(0,0) = TRINUM(0) + 0 = 0.  Step: given
;;; NNPAIR(i, j) = n, split on i (nn-zero-or-succ) --
;;;   i = 0       : NNPAIR(succ j, 0) = TRINUM(succ j)     = TRINUM(j) + succ j
;;;                                   = succ(TRINUM(j) + j) = succ(n)
;;;   i = succ q  : NNPAIR(q, succ j)  = TRINUM(succ(q+j)) + succ j
;;;                                   = succ(TRINUM(succ q + j) + j) = succ(n)
;;; -- which is the antidiagonal walk, one step down or on to the next diagonal.
(sp (make-wff
  '(FORALL n_ (IMPLIES (IN n_ NN)
      (FORSOME i_ (AND (IN i_ NN)
        (FORSOME j_ (AND (IN j_ NN) (= (NNPAIR i_ j_) n_)))))))))
(ni)

;; base: the witnesses are (0, 0)
(dk-focus-goal! "= 0)")
(dk-ew-split! 0
         (lambda () (arith))
         (lambda ()
           (dk-ew-split! 0
                    (lambda () (arith))
                    (lambda () (mac 'nnpair) (arith) (mac 'trinum-zero) (arith)))))

;; step: peel n, peel the IH, and open both of the IH's existentials
(dk-focus-goal! "succ(n_))")
(di) (di)
(dk-ai-head! 'FORSOME) (dk-ai-head! 'AND)
(dk-ai-head! 'FORSOME) (dk-ai-head! 'AND)

;; the eigenvariables are READ OFF the landed equation, not guessed
(define np2-eq
  (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                 (pair? (cadr a)) (eq? (car (cadr a)) 'NNPAIR)))
                (dk-asms))
      (error "nn-pairing: the IH equation did not land")))
(define np2-i (cadr  (cadr np2-eq)))
(define np2-j (caddr (cadr np2-eq)))

(define np2-cases
  (begin (fact 'nn-zero-or-succ np2-i)
         (dk-opened (lambda () (dk-ai-head! 'OR)))))

;; -- case i = 0 : witnesses (succ j, 0)
(define (np2-case-zero!)
  (subst `(= n_ (NNPAIR ,np2-i ,np2-j)))
  (subst `(= ,np2-i 0))
  (mac 'nnpair)
  (fact 'nn-add-zero `(succ ,np2-j))
  (subst `(= (+ (succ ,np2-j) 0) (succ ,np2-j)))
  (np2-comm! 0 np2-j)
  (subst `(= (+ 0 ,np2-j) (+ ,np2-j 0)))
  (fact 'nn-add-zero np2-j)
  (subst `(= (+ ,np2-j 0) ,np2-j))
  (fact 'trinum-type `(succ ,np2-j))
  (fact 'nn-add-zero `(TRINUM (succ ,np2-j)))
  (subst `(= (+ (TRINUM (succ ,np2-j)) 0) (TRINUM (succ ,np2-j))))
  (mac 'trinum-succ)
  (fact 'trinum-type np2-j)
  (fact 'nn-add-succ `(TRINUM ,np2-j) np2-j)
  (subst `(= (+ (TRINUM ,np2-j) (succ ,np2-j)) (succ (+ (TRINUM ,np2-j) ,np2-j))))
  (np2-defined-succ-sum! `(TRINUM ,np2-j) np2-j)
  (rfl))

(dk-focus-ctx! `(= ,np2-i 0) np2-cases)
(fact 'nn-succ-closed np2-j)
(dk-ew-split! `(succ ,np2-j)
         (lambda () (ass))
         (lambda () (dk-ew-split! 0 (lambda () (arith)) np2-case-zero!)))

;; -- case i = succ q : witnesses (q, succ j)
(define np2-q #f)
(define (np2-case-succ!)
  (subst `(= n_ (NNPAIR ,np2-i ,np2-j)))
  (subst `(= ,np2-i (succ ,np2-q)))
  (mac 'nnpair)
  (fact 'nn-add-succ np2-q np2-j)
  (subst `(= (+ ,np2-q (succ ,np2-j)) (succ (+ ,np2-q ,np2-j))))
  (fact 'tab-succ-add np2-q np2-j)
  (subst `(= (+ (succ ,np2-q) ,np2-j) (succ (+ ,np2-q ,np2-j))))
  (np2-sum-type! np2-q np2-j)
  (fact 'nn-succ-closed `(+ ,np2-q ,np2-j))
  (fact 'trinum-type `(succ (+ ,np2-q ,np2-j)))
  (fact 'nn-add-succ `(TRINUM (succ (+ ,np2-q ,np2-j))) np2-j)
  (subst `(= (+ (TRINUM (succ (+ ,np2-q ,np2-j))) (succ ,np2-j))
             (succ (+ (TRINUM (succ (+ ,np2-q ,np2-j))) ,np2-j))))
  (np2-defined-succ-sum! `(TRINUM (succ (+ ,np2-q ,np2-j))) np2-j)
  (rfl))

(dk-focus-goal! "succ(n_)")
(dk-ai-head! 'FORSOME)
(dk-ai-head! 'AND)
(set! np2-q
      (let ((eqq (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                                (eq? (cadr a) np2-i)
                                                (pair? (caddr a))
                                                (eq? (car (caddr a)) 'succ)))
                               (dk-asms))
                     (error "nn-pairing: no i = succ q in the second case"))))
        (cadr (caddr eqq))))
(fact 'nn-succ-closed np2-j)
(dk-ew-split! np2-q
         (lambda () (ass))
         (lambda () (dk-ew-split! `(succ ,np2-j) (lambda () (ass)) np2-case-succ!)))
(qed 'nnpair-onto)

(topic! 'trinum-type  'inequalities)
(topic! 'trinum-mono  'inequalities)
(topic! 'nnpair-onto  'inequalities)

;;; ---- injectivity -------------------------------------------------------
;;; Three rungs and the theorem.  The argument is the one sketched in the note
;;; this replaces, and it needed one lemma the library did not have:
;;; `nn-le-antisym' (nn-order-proof.scm, proved there from rr-leq-antisymmetric,
;;; since <= on NN IS the RR order restricted).
;;;
;;; Two mechanical points cost a cycle each and are worth recording:
;;;   * `di' peels the FORALL block plus ONE implication when the statement is
;;;     built FLAT by forall-guarded (all binders outermost, then the guards).
;;;     Counting `di's is therefore wrong here as everywhere: np2-peel! loops
;;;     and errors if a call makes no progress.
;;;   * `mac' will not unfold NNPAIR while the equation is still under the four
;;;     binders.  Peel the TYPINGS first (np2-peel-types!, which stops at the
;;;     first non-(IN _ _) antecedent), unfold on the quantifier-free goal, then
;;;     peel the rest.  Unfolding in the ASSUMPTION is not an option: `mac-h'
;;;     cannot unfold a def-functoid.

;;; peel while the goal is FORALL/IMPLIES; error rather than spin.
(define (np2-peel!)
  (let loop ((fuel 14))
    (let ((g (dk-goal)))
      (when (and (> fuel 0) (pair? g) (memq (car g) '(FORALL IMPLIES)))
        (di)
        (if (equal? (dk-goal) g) (error "np2-peel!: no progress at" g) (loop (- fuel 1)))))))

;;; peel FORALLs and (IN _ _) antecedents only -- stop at the real hypothesis.
(define (np2-peel-types!)
  (let loop ((fuel 14))
    (let ((g (dk-goal)))
      (when (and (> fuel 0) (pair? g)
                 (or (eq? (car g) 'FORALL)
                     (and (eq? (car g) 'IMPLIES) (pair? (cadr g)) (eq? (car (cadr g)) 'IN))))
        (di)
        (if (equal? (dk-goal) g) (error "np2-peel-types!: no progress at" g)
            (loop (- fuel 1)))))))

;;; `have!' is alpha-idempotent-hostile: cutting a claim ALREADY in context is
;;; the self-loop the kernel guards against, and have! errors on it.  These
;;; proofs re-establish the same typings in nested branches, so guard the cut.
(define (np2-have! f)
  (if (any-pred (lambda (a) (alpha-equiv? a f)) (dk-asms)) 'given (have! f)))
(define (np2-sum! x y) (np2-have! `(AND (IN ,x NN) (IN ,y NN))) (fact 'nn-add-closed x y))
(define (np2-comm2! x y) (np2-have! `(AND (IN ,x NN) (IN ,y NN))) (fact 'nn-add-comm x y))

;;; nnpair-diag-bound: j <= s  =>  succ(TRINUM(s) + j) <= TRINUM(succ s).
;;; The whole antidiagonal s sits below the start of antidiagonal succ s.
(sp (make-wff (forall-guarded '(s_ j_) (list '(IN s_ NN) '(IN j_ NN) '(<= j_ s_))
                '(<= (succ (+ (TRINUM s_) j_)) (TRINUM (succ s_))))))
(np2-peel!)
(fact 'trinum-type 's_)
(fact 'nn-add-le-mono 's_ '(TRINUM s_) 'j_)
(np2-sum! '(TRINUM s_) 'j_)
(np2-sum! '(TRINUM s_) 's_)
(fact 'nn-succ-mono '(+ (TRINUM s_) j_) '(+ (TRINUM s_) s_))
(mac 'trinum-succ)
(fact 'nn-succ-closed 's_)
(fact 'nn-add-succ '(TRINUM s_) 's_)
(subst '(= (+ (TRINUM s_) (succ s_)) (succ (+ (TRINUM s_) s_))))
(ass)
(qed 'nnpair-diag-bound)

;;; nnpair-cross: a code on antidiagonal s is STRICTLY below any code on a
;;; later antidiagonal t.  This is the whole content of injectivity's hard half.
(sp (make-wff (forall-guarded '(s_ t_ j_ k_)
                (list '(IN s_ NN) '(IN t_ NN) '(IN j_ NN) '(IN k_ NN)
                      '(<= j_ s_) '(<= (succ s_) t_))
                '(<= (succ (+ (TRINUM s_) j_)) (+ (TRINUM t_) k_)))))
(np2-peel!)
(fact 'nnpair-diag-bound 's_ 'j_)
(fact 'nn-succ-closed 's_)
(fact 'trinum-mono 't_ '(succ s_))
(fact 'trinum-type 't_)
(fact 'nn-le-add-right 'k_ '(TRINUM t_))
;; Typings for the guarded nn-le-trans (2026-08-02): the three terms it chains
;; through here -- succ(TRINUM(s_)+j_), TRINUM(succ s_), TRINUM(t_)+k_ -- were
;; never typed, which the unguarded statement let this proof get away with.
(fact 'trinum-type 's_)
(fact 'trinum-type '(succ s_))
(np2-sum-type! '(TRINUM s_) 'j_)
(fact 'nn-succ-closed '(+ (TRINUM s_) j_))
(np2-sum-type! '(TRINUM t_) 'k_)
(fact 'nn-le-trans-guarded '(succ (+ (TRINUM s_) j_)) '(TRINUM (succ s_)) '(TRINUM t_))
(fact 'nn-le-trans-guarded '(succ (+ (TRINUM s_) j_)) '(TRINUM t_) '(+ (TRINUM t_) k_))
(ass)
(qed 'nnpair-cross)

;;; nnpair-inj.  Antidiagonals first: neither sum can exceed the other, because
;;; nnpair-cross would put the two codes strictly apart while the hypothesis says
;;; they are equal.  `pbc' supplies the classical step, nn-le-antisym closes it,
;;; and two cancellations finish.
(sp (make-wff (forall-guarded '(i_ j_ ii_ jj_)
                (list '(IN i_ NN) '(IN j_ NN) '(IN ii_ NN) '(IN jj_ NN))
                '(IMPLIES (= (NNPAIR i_ j_) (NNPAIR ii_ jj_))
                          (AND (= i_ ii_) (= j_ jj_))))))
(np2-peel-types!)
(mac 'nnpair)
(np2-peel!)
(np2-sum! 'i_ 'j_)
(np2-sum! 'ii_ 'jj_)
(fact 'nn-le-add-left 'i_ 'j_)
(fact 'nn-le-add-left 'ii_ 'jj_)

(define np2-ss '(+ i_ j_))
(define np2-tt '(+ ii_ jj_))
(define (np2-tr x) `(TRINUM ,x))
(define np2-heq `(= (+ ,(np2-tr np2-ss) j_) (+ ,(np2-tr np2-tt) jj_)))
(define np2-sseq `(= ,np2-ss ,np2-tt))
(define np2-trs (np2-tr np2-ss))

;;; one side of the trichotomy: assume the sums are the wrong way round and let
;;; nnpair-cross contradict the hypothesis.  x,y are the sums; xj,yj their j's.
(define (np2-side! x xj y yj)
  (lambda ()
    (pbc)                                          ; assume NOT(x <= y), goal FALSITY
    (fact 'nn-not-le-succ-le x y)                  ; ... so succ y <= x
    (fact 'trinum-type x)
    (fact 'trinum-type y)
    (np2-sum! (np2-tr y) yj)
    (np2-sum! (np2-tr x) xj)
    (fact 'nnpair-cross y x yj xj)                 ; succ(TR(y)+yj) <= TR(x)+xj
    (fact 'nn-succ-le-antisym `(+ ,(np2-tr y) ,yj) `(+ ,(np2-tr x) ,xj))
    (have! `(<= (+ ,(np2-tr x) ,xj) (+ ,(np2-tr y) ,yj))
           (lambda () (subst np2-heq)
                      (fact 'nn-le-refl `(+ ,(np2-tr np2-tt) jj_))
                      (ass)))
    (ai `(NOT (<= (+ ,(np2-tr x) ,xj) (+ ,(np2-tr y) ,yj))))))

(have! `(<= ,np2-ss ,np2-tt) (np2-side! np2-ss 'j_ np2-tt 'jj_))
(have! `(<= ,np2-tt ,np2-ss) (np2-side! np2-tt 'jj_ np2-ss 'j_))
(fact 'nn-le-antisym np2-ss np2-tt)                ; the antidiagonals coincide

;;; j = jj: commute both sides so nn-add-cancel (which cancels on the RIGHT)
;;; applies, then rewrite with the hypothesis and with s = t.
(have! `(= j_ jj_)
  (lambda ()
    (have! `(= (+ j_ ,np2-trs) (+ jj_ ,np2-trs))
      (lambda ()
        (fact 'trinum-type np2-ss)
        (np2-comm2! 'j_ np2-trs)  (subst `(= (+ j_ ,np2-trs) (+ ,np2-trs j_)))
        (np2-comm2! 'jj_ np2-trs) (subst `(= (+ jj_ ,np2-trs) (+ ,np2-trs jj_)))
        (subst np2-heq)
        (subst np2-sseq)
        (fact 'trinum-type np2-tt)
        (np2-sum! (np2-tr np2-tt) 'jj_)
        (rfl)))
    (fact 'trinum-type np2-ss)
    (fact 'nn-add-cancel 'j_ 'jj_ np2-trs)
    (ass)))

;;; i = ii: with jj = j, s = t is already the cancellable shape.  The middle
;;; step rewrites the COMPOUND term (i + jj), not the variable jj everywhere --
;;; `subst' rewrites every occurrence, so the equation handed to it must be the
;;; one whose left side appears exactly where the rewrite is wanted.
(have! `(= i_ ii_)
  (lambda ()
    (have! `(= jj_ j_) (lambda () (subst `(= j_ jj_)) (rfl)))
    (have! `(= (+ i_ jj_) (+ ii_ jj_))
      (lambda ()
        (have! `(= (+ i_ jj_) (+ i_ j_)) (lambda () (subst `(= jj_ j_)) (rfl)))
        (subst `(= (+ i_ jj_) (+ i_ j_)))
        (ass)))
    (fact 'nn-add-cancel 'i_ 'ii_ 'jj_)
    (ass)))

(for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (di))))
(qed 'nnpair-inj)

(topic! 'nnpair-diag-bound 'inequalities)
(topic! 'nnpair-cross      'inequalities)
(topic! 'nnpair-inj        'combinatorial)

;;; ---- the projections ---------------------------------------------------
;;; NNFST(n) / NNSND(n) are definite descriptions: THE i (resp. j) such that
;;; some pair starting (resp. ending) there codes n.  nnpair-onto makes the
;;; description non-empty, nnpair-inj makes it unique -- which is exactly the
;;; pair of obligations `iota-d' posts, so the two theorems above are precisely
;;; what this construction consumes.
;;;
;;; This is the FIRST use of the `iota-def' kernel rule in the library; before
;;; today the load's kernel-rules-audit listed it among the tags no proof
;;; exercises.  It behaved as documented (primitive-inferences.scm:1261).

;;; nnpair-type: a code is a natural.  Wanted for the definedness side of `rfl'.
(sp (make-wff (forall-guarded '(i_ j_) (list '(IN i_ NN) '(IN j_ NN))
                '(IN (NNPAIR i_ j_) NN))))
(np2-peel!)
(mac 'nnpair)
(np2-sum! 'i_ 'j_)
(fact 'trinum-type '(+ i_ j_))
(np2-sum! '(TRINUM (+ i_ j_)) 'j_)
(ass)
(qed 'nnpair-type)

(def-functoid 'NNFST '(n_)
  '(IOTA a_ (AND (IN a_ NN)
                 (FORSOME b_ (AND (IN b_ NN) (= (NNPAIR a_ b_) n_))))))
(def-functoid 'NNSND '(n_)
  '(IOTA b_ (AND (IN b_ NN)
                 (FORSOME a_ (AND (IN a_ NN) (= (NNPAIR a_ b_) n_))))))
(notation! 'NNFST 'kind 'functoid 'arity 1 'english "the first component of $1")
(notation! 'NNSND 'kind 'functoid 'arity 1 'english "the second component of $1")

;;; context helpers for the two projection proofs.
(define (np2-first h)                   ; first context formula with head h
  (let ((fs (filter (lambda (f) (and (pair? f) (eq? (car f) h))) (dk-asms))))
    (if (null? fs) (error "np2-first: no context formula with head" h) (car fs))))
;; `ai' on a FORSOME lands its body as ONE conjunction, so split after opening.
(define (np2-open-ex!) (ai (np2-first 'FORSOME)) (dk-split! (np2-first 'AND)))
(define (np2-go! h)                     ; focus the unique open leaf with head h
  (let ((ns (filter (lambda (n) (let ((g (dk-goal-of n))) (and (pair? g) (eq? (car g) h))))
                    (proof-leaves))))
    (if (= 1 (length ns)) (dk-focus! (car ns))
        (error "np2-go!: leaf with this head is not unique" h (length ns)))))

;;; The two projection proofs differ only in which slot the description binds
;;; and which conjunct of nnpair-inj answers it, so the driver is written once.
;;; MINE is the component being computed, OTHER the one existentially quantified
;;; away; PAIR builds the NNPAIR argument list from (bound-var, witness).
(define (np2-proj! unfold mine other pair)
  (np2-peel!)
  (mac unfold)
  (let ((ioterm (cadr (dk-goal))))
    (fact 'nnpair-type 'i_ 'j_)
    (iota-d ioterm)
    ;; obligation 1: existence (witness MINE) and uniqueness (nnpair-inj)
    (np2-go! 'FORSOME)
    (ew mine)
    (for-each
      (lambda (n)
        (dk-focus! n)
        (if (eq? (car (dk-goal)) 'FORALL)
            (begin                                        ; uniqueness
              (np2-peel!)
              (dk-split! (np2-first 'AND))
              (np2-open-ex!)
              (let* ((eq (np2-first '=))
                     (ar (cdr (cadr eq)))                 ; the NNPAIR arguments
                     (y  (car (pair 'bound ar)))
                     (b  (cdr (pair 'bound ar))))
                (fact 'nnpair-inj (car ar) (cadr ar) 'i_ 'j_)
                (dk-split! `(AND (= ,(car ar) i_) (= ,(cadr ar) j_)))
                (subst `(= ,y ,mine))
                (rfl)))
            (for-each                                     ; the witness works
              (lambda (m)
                (dk-focus! m)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (ew other)
                           (for-each (lambda (k)
                                       (dk-focus! k)
                                       (if (eq? (car (dk-goal)) 'IN) (ass) (rfl)))
                                     (dk-opened (lambda () (di)))))))
              (dk-opened (lambda () (di))))))
      (dk-opened (lambda () (di))))
    ;; obligation 2: read the answer off the defining property
    (np2-go! '=)
    (dk-split! (np2-first 'AND))
    (np2-open-ex!)
    (let* ((eq (np2-first '=))
           (ar (cdr (cadr eq))))
      (fact 'nnpair-inj (car ar) (cadr ar) 'i_ 'j_)
      (dk-split! `(AND (= ,(car ar) i_) (= ,(cadr ar) j_)))
      (ass))))

;;; NNFST(NNPAIR(i,j)) = i.  The description binds the FIRST slot, so the
;;; equation nnpair-inj hands back is its first conjunct.
(sp (make-wff (forall-guarded '(i_ j_) (list '(IN i_ NN) '(IN j_ NN))
                '(= (NNFST (NNPAIR i_ j_)) i_))))
(np2-proj! 'nnfst 'i_ 'j_ (lambda (tag ar) (cons (car ar) (cadr ar))))
(qed 'nnfst-nnpair)

;;; NNSND(NNPAIR(i,j)) = j.  Same argument, second slot.
(sp (make-wff (forall-guarded '(i_ j_) (list '(IN i_ NN) '(IN j_ NN))
                '(= (NNSND (NNPAIR i_ j_)) j_))))
(np2-proj! 'nnsnd 'j_ 'i_ (lambda (tag ar) (cons (cadr ar) (car ar))))
(qed 'nnsnd-nnpair)

;;; ---- the projections are TOTAL -----------------------------------------
;;; (IN (NNFST n) NN) for every n in NN.  Same iota-d shape, but the witness
;;; now comes from nnpair-onto rather than from the goal: n is SOME code, and
;;; that pair is the description's witness.  PICK selects the component this
;;; projection binds.
(define (np2-projtype! unfold pick)
  (np2-peel!)
  (mac unfold)
  (let ((ioterm (cadr (dk-goal))))
    (iota-d ioterm)
    (np2-go! 'FORSOME)
    (fact 'nnpair-onto 'n_)
    (np2-open-ex!)                                   ; eigenvar i0
    (np2-open-ex!)                                   ; eigenvar j0 + the equation
    (let* ((oeq (np2-first '=))
           (i0 (cadr  (cadr oeq)))
           (j0 (caddr (cadr oeq)))
           (mine  (pick i0 j0))
           (other (pick j0 i0)))
      (ew mine)
      (for-each
        (lambda (n)
          (dk-focus! n)
          (if (eq? (car (dk-goal)) 'FORALL)
              (begin                                  ; uniqueness
                (np2-peel!)
                (dk-split! (np2-first 'AND))
                (np2-open-ex!)
                (let* ((eq (np2-first '=))
                       (ar (cdr (cadr eq))))
                  ;; both pairs code n, so they are equal -- chain through n.
                  (have! `(= (NNPAIR ,(car ar) ,(cadr ar)) (NNPAIR ,i0 ,j0))
                         (lambda () (subst oeq) (ass)))
                  (fact 'nnpair-inj (car ar) (cadr ar) i0 j0)
                  (dk-split! `(AND (= ,(car ar) ,i0) (= ,(cadr ar) ,j0)))
                  (subst `(= ,(pick (car ar) (cadr ar)) ,mine))
                  (rfl)))
              (for-each                               ; the witness works
                (lambda (m)
                  (dk-focus! m)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (ew other)
                             (for-each (lambda (k) (dk-focus! k) (ass))
                                       (dk-opened (lambda () (di)))))))
                (dk-opened (lambda () (di))))))
        (dk-opened (lambda () (di))))
      ;; obligation 2: the defining property's FIRST conjunct is the goal
      (np2-go! 'IN)
      (dk-split! (np2-first 'AND))
      (ass))))

(sp (make-wff (forall-guarded '(n_) (list '(IN n_ NN)) '(IN (NNFST n_) NN))))
(np2-projtype! 'nnfst (lambda (p q) p))
(qed 'nnfst-type)

(sp (make-wff (forall-guarded '(n_) (list '(IN n_ NN)) '(IN (NNSND n_) NN))))
(np2-projtype! 'nnsnd (lambda (p q) q))
(qed 'nnsnd-type)

(topic! 'nnpair-type  'plumbing)
(topic! 'nnfst-type   'plumbing)
(topic! 'nnsnd-type   'plumbing)
(topic! 'nnfst-nnpair 'combinatorial)
(topic! 'nnsnd-nnpair 'combinatorial)

;;; ---- the flattening ----------------------------------------------------
;;; nn-flatten: for h : NN -> (NN -> A) there is e : NN -> A whose range
;;; contains every h(i)(j).  This is the fact everything downstream actually
;;; consumes -- re-indexing a doubly indexed family by a single natural.
;;;
;;; The witness is the obvious one, e = \n. h(NNFST n)(NNSND n), and it works
;;; precisely because NNFST/NNSND are total (nnfst-type, nnsnd-type) and invert
;;; the coding (nnfst-nnpair, nnsnd-nnpair).  Note there is NO appeal to CHOICE
;;; anywhere in this file: onto plus injective is exactly enough.
;;;
;;; Two mechanical points, both instances of rules recorded in CLAUDE.md:
;;;   * `lam-t' RENAMES the lambda binder, so the body obligation is about a
;;;     fresh variable.  Read it off the goal; citing the source name misses.
;;;   * NNFST(NNPAIR(i,j)) sits inside (h_ ...), which is itself the OPERATOR of
;;;     the outer application, and `subst' reaches argument positions only.  The
;;;     projection equations must be applied as MACETES.  (`subst' silently
;;;     no-ops otherwise -- the goal comes back with one projection reduced and
;;;     the other untouched, which is what the failure looks like.)
(sp (make-wff (forall-guarded '(aa_ h_) (list '(IN h_ (FUN NN (FUN NN aa_))))
  `(FORSOME e_ (AND (IN e_ (FUN NN aa_))
     ,(forall-guarded '(i_ j_) (list '(IN i_ NN) '(IN j_ NN))
        '(FORSOME m_ (AND (IN m_ NN) (= (e_ m_) ((h_ i_) j_))))))))))
(np2-peel!)
(ew '(VNB-LAMBDA n_ NN ((h_ (NNFST n_)) (NNSND n_))))
(for-each
  (lambda (n)
    (dk-focus! n)
    (if (eq? (car (dk-goal)) 'IN)
        (begin                                   ; e is a function NN -> aa_
          (dk-lam-t!)
          (let ((v (cadr (dk-goal))))            ; lam-t renames the binder
            (np2-peel!)
            (fact 'nnfst-type v)
            (fact 'nnsnd-type v)
            (fact 'fun-apply-type-c 'h_ 'NN '(FUN NN aa_) `(NNFST ,v))
            (fact 'fun-apply-type-c `(h_ (NNFST ,v)) 'NN 'aa_ `(NNSND ,v)))
          (ass))
        (begin                                   ; every h(i)(j) is hit, at NNPAIR(i,j)
          (np2-peel!)
          (ew '(NNPAIR i_ j_))
          (for-each
            (lambda (m)
              (dk-focus! m)
              (if (eq? (car (dk-goal)) 'IN)
                  (begin (fact 'nnpair-type 'i_ 'j_) (ass))
                  (begin
                    ;; e_ has domain NN and is applied at the CODE, so the code's
                    ;; typing licenses the reduction.  The sibling branch cites
                    ;; the same fact for its (IN (NNPAIR i_ j_) NN) goal.
                    (fact 'nnpair-type 'i_ 'j_)
                    (lam-b)
                    (mac 'nnfst-nnpair)
                    (mac 'nnsnd-nnpair)
                    (fact 'fun-apply-type-c 'h_ 'NN '(FUN NN aa_) 'i_)
                    (fact 'fun-apply-type-c '(h_ i_) 'NN 'aa_ 'j_)
                    (rfl))))
            (dk-opened (lambda () (di)))))))
  (dk-opened (lambda () (di))))
(qed 'nn-flatten)
(topic! 'nn-flatten 'combinatorial)

;;; ---- WHAT REMAINS ------------------------------------------------------
;;; Nothing in this file.  The re-indexing mechanism is complete: NNPAIR is a
;;; bijection NN x NN -> NN (nnpair-onto, nnpair-inj), NNFST/NNSND invert it,
;;; and nn-flatten delivers the single sequence.  Its first consumer landed on
;;; 2026-08-07: `compact-metric-is-separable' is PROVEN in
;;; theorem-library/compact-separable-proof.scm (loaded immediately after this
;;; file), with nn-flatten collapsing the scale-indexed family of nets into the
;;; single dense sequence IS-SEPARABLE asks for.  Still downstream and still
;;; asserted: `coordinatewise-diagonal-subseq' and the countable unions of
;;; sigma-algebra.scm.
