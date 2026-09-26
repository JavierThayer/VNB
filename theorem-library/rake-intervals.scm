;;; rake-intervals.scm -- the interval / monus-predecessor supports of
;;; structure-library/order-lemmas.scm, PROVEN (batch K, 2026-09-17).
;;;
;;; WHAT IS PROVED, and where each statement came from (copied byte-for-byte
;;; from the support site unless the line says GUARDED):
;;;
;;;   nn-succ-le-cancel   structure-library/order-lemmas.scm:345
;;;   nn-minus-succ-1     structure-library/order-lemmas.scm:247
;;;   one-in-interval     structure-library/order-lemmas.scm:255
;;;   succ-not-one        structure-library/order-lemmas.scm:275
;;;   nn-minus-1-inj      structure-library/order-lemmas.scm:282
;;;   succ-in-interval   order-lemmas.scm:269  + (IN q NN)   -- see below
;;;   pred-in-interval   order-lemmas.scm:260  + (IN p NN)   -- see below
;;;
;;; THE HELPER THE BRIEF ASKED FOR IS ALREADY IN THE TREE, UNDER ANOTHER NAME.
;;; `nn-succ-le-succ' (succ a <= succ b => a <= b) is exactly
;;; `nn-succ-le-cancel', an ASSERTED support at order-lemmas.scm:345 -- so it is
;;; proved here under THAT name and the support retires, rather than a second
;;; name being added for the same fact.  order-lemmas.scm's own note says it did
;;; not move in 2026-08-24 because "no bill in the library names it"; that is a
;;; reason not to prioritise it, not a reason to duplicate it.  The proof is the
;;; one rake-mat-typing.scm's `rkm-pred-in-interval!' runs inline: assume
;;; NOT(a <= b), so succ b <= a (nn-not-le-succ-le), chain it with the hypothesis
;;; to succ a <= a, and nn-succ-le-antisym then denies a <= a, which nn-le-refl
;;; asserts.
;;;
;;; TWO STATEMENTS ARE FALSE AS WRITTEN, and the defect is the same in both:
;;; the interval's UPPER BOUND is never typed.
;;;
;;;   succ-in-interval  forall q, z.  z in [1,q]  =>  succ z in [1, succ q]
;;;   pred-in-interval  forall p, i.  i in [1, succ p] => i /= 1
;;;                                   => NN-MINUS(i,1) in [1,p]
;;;
;;; INTERVAL(1,b) is { i in NN : 1 <= i and i <= b } (a def-functoid,
;;; structure-library/matrix.scm), so it is a perfectly good set for a bound b
;;; OUTSIDE NN -- INTERVAL(1, 3/2) is {1} -- while EVERY axiom and theorem about
;;; `succ' is guarded on NN (nn-succ-closed, nn-succ-mono, nn-succ-plus-one,
;;; nn-one-le-succ, ...; `succ' off NN is an uninterpreted application, which is
;;; the same observation comb-kk-laws.scm makes about bt-succ-minus-1 over ZZ).
;;; So `succ q' is unconstrained when q is not a natural, and a model may
;;; interpret it however it likes.  Countermodels:
;;;
;;;   succ-in-interval  q := 3/2, with succ(3/2) interpreted as 0.
;;;                     INTERVAL(1, 3/2) = {1}, so z := 1 satisfies the premise;
;;;                     succ 1 = 2 and INTERVAL(1, 0) is EMPTY.
;;;   pred-in-interval  p := 1/2, with succ(1/2) interpreted as 100.
;;;                     i := 2 is in INTERVAL(1,100) and i /= 1, but
;;;                     NN-MINUS(2,1) = 1 and INTERVAL(1, 1/2) is EMPTY.
;;;
;;; Both are proved here in their GUARDED form, with (IN q NN) / (IN p NN) added
;;; outermost and nothing else touched, under the names succ-in-interval
;;; and pred-in-interval.  The supports are NOT retired by this file --
;;; the integrator decides.  (Every citer measured supplies the typing already:
;;; border-mult-proof.scm:198 has `q' as a MAT dimension, border-assembly,
;;; bordered-eq-border and smith-staircase all pass a dimension read off a
;;; matrix.  So the guard is expected to cost the citers one `fact' at most.)
;;;
;;; LOAD WINDOW [220, 350) -- 0-based over load.scm's `*vnb-files*' entries.
;;;   lo = 220, immediately after theorem-library/nn-order-via-rr (219), the
;;;        LATEST citation: nn-succ-le-antisym lives there.  The others are
;;;        earlier -- comb-kk-laws 213 (bt-succ-minus-1), nn-parity-proof 212
;;;        (nn-nonzero-is-succ), nn-order-basics 169 (nn-le-refl,
;;;        nn-le-trans-guarded), nn-not-le-succ-le 168, nn-order-ord 167
;;;        (nn-one-in, nn-succ-mono, nn-one-le-succ), interval-mem-intro 152,
;;;        interval-basics 151 (interval-elt-in-nn / -lo / -hi), finsum-additive
;;;        118 (nn-minus-def), number-systems 34 (nn-succ-closed).
;;;   hi = 350, theorem-library/border-mult-proof, the earliest citer of any of
;;;        the seven (it cites one-in-interval, succ-in-interval, succ-not-one,
;;;        nn-minus-succ-1 and pred-in-interval).  The later citers are
;;;        border-assembly 351 (pred-in-interval, nn-minus-1-inj),
;;;        bordered-eq-border 352, clear-pivot-cross 353,
;;;        smith-diagonalization 354, smith-staircase 355 (nn-succ-le-cancel).
;;;        One position serves all seven.
;;;
;;; Helper prefix: rkk-.

;;; ---- file-local drivers ------------------------------------------------

;; Report open goals loudly rather than qed a half proof.
(define (rkk-done! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-intervals: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline)
                    (for-each (lambda (a)
                                (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-intervals: unfinished" name))))

;; (rkk-if-true! IFTERM THUNK) -- `if-true' opens TWO leaves: the CONDITION and
;; the MAIN goal, which gains (= IFTERM then-branch) as an ASSUMPTION -- the
;; goal itself is NOT rewritten, hence the explicit `subst'.  The condition leaf
;; is discriminated on its GOAL, never on where focus landed.  THUNK runs on the
;; main leaf.  (rkm-if-branch!, rake-mat-typing.scm, is the same helper.)
(define (rkk-if-true! ifterm thunk)
  (let* ((c      (cadr ifterm))
         (val    (caddr ifterm))
         (opened (dk-opened (lambda () (if-true ifterm))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) c)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "rkk-if-true!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (thunk)))

;; (rkk-pred! V) -- with (IN V NN) and (<= 1 V) in context, land
;; (IN Z NN), (= V (succ Z)) and (= (NN-MINUS V 1) Z) for a fresh Z, and
;; return Z.  The monus predecessor, read off through nn-nonzero-is-succ and
;; nn-minus-succ-1 (proved just above).
(define (rkk-pred! v)
  (dk-nonzero! v)
  (let* ((ex (dk-fact! 'nn-nonzero-is-succ v))
         (z  (dk-skolem! ex))
         (eq (list '= (list 'NN-MINUS v 1) z)))
    (fact 'nn-minus-succ-1 z)                  ; (= (NN-MINUS (succ z) 1) z)
    (have! eq (lambda () (subst (list '= v (list 'succ z))) (ass)))
    (dk-focus-having! eq)
    z))

;;; =======================================================================
;;; nn-succ-le-cancel:  succ a <= succ b  =>  a <= b.
;;; Statement: structure-library/order-lemmas.scm:345, unchanged.
;;; =======================================================================
(sp (make-wff '(FORALL a (IMPLIES (IN a NN) (FORALL b (IMPLIES (IN b NN)
     (IMPLIES (<= (succ a) (succ b)) (<= a b))))))))
(dk-peel!)
(fact 'nn-succ-closed 'a)
(fact 'nn-succ-closed 'b)
(use-em '(<= a b)
  (lambda () (ass))
  (lambda ()                            ; NOT (a <= b), so succ b <= a ...
    (fact 'nn-not-le-succ-le 'a 'b)
    (fact 'nn-le-trans-guarded '(succ a) '(succ b) 'a)   ; ... hence succ a <= a
    (fact 'nn-succ-le-antisym 'a 'a)                     ; which denies a <= a
    (fact 'nn-le-refl 'a)
    (ai '(NOT (<= a a)))))
(rkk-done! 'nn-succ-le-cancel)
(topic! 'nn-succ-le-cancel 'inequalities)

;;; =======================================================================
;;; nn-minus-succ-1:  NN-MINUS(succ z, 1) = z.
;;; Statement: structure-library/order-lemmas.scm:247, unchanged.
;;; nn-minus-def unfolds the monus to the IF, 1 <= succ z takes its true
;;; branch, and bt-succ-minus-1 does the integer step.
;;; =======================================================================
(sp (make-wff '(FORALL z (IMPLIES (IN z NN) (= (NN-MINUS (succ z) 1) z)))))
(dk-peel!)
(fact 'nn-one-in)
(fact 'nn-succ-closed 'z)
(fact 'nn-one-le-succ 'z)                       ; 1 <= succ z
(fact 'bt-succ-minus-1 'z)                      ; (succ z) - 1 = z
(fact 'nn-minus-def '(succ z) 1)
(subst '(= (NN-MINUS (succ z) 1) (IF (<= 1 (succ z)) (- (succ z) 1) 0)))
(rkk-if-true! '(IF (<= 1 (succ z)) (- (succ z) 1) 0) (lambda () (ass)))
(rkk-done! 'nn-minus-succ-1)
(topic! 'nn-minus-succ-1 'plumbing)

;;; =======================================================================
;;; one-in-interval:  1 in [1, succ n].
;;; Statement: structure-library/order-lemmas.scm:255, unchanged.
;;; =======================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN 1 (INTERVAL 1 (succ n)))))))
(dk-peel!)
(fact 'nn-one-in)
(fact 'nn-le-refl 1)
(fact 'nn-one-le-succ 'n)
(fact 'interval-mem-intro 1 '(succ n) 1)
(ass)
(rkk-done! 'one-in-interval)
(topic! 'one-in-interval 'inequalities)

;;; =======================================================================
;;; succ-not-one:  z in [1,q]  =>  succ z /= 1.
;;; Statement: structure-library/order-lemmas.scm:275, unchanged -- and it needs
;;; NO typing of q: everything comes off z.  succ z = 1 <= z is succ z <= z,
;;; which nn-succ-le-antisym turns into NOT (z <= z).
;;; =======================================================================
(sp (make-wff '(FORALL q (FORALL z (IMPLIES (IN z (INTERVAL 1 q))
     (NOT (= (succ z) 1)))))))
(dk-peel!)
(di)                                            ; assume succ z = 1; goal FALSITY
(fact 'interval-elt-in-nn 1 'q 'z)
(fact 'interval-lo 1 'q 'z)                     ; 1 <= z
(fact 'nn-succ-closed 'z)
(have! '(<= (succ z) z) (lambda () (subst '(= (succ z) 1)) (ass)))
(dk-focus-having! '(<= (succ z) z))
(fact 'nn-succ-le-antisym 'z 'z)
(fact 'nn-le-refl 'z)
(ai '(NOT (<= z z)))
(rkk-done! 'succ-not-one)
(topic! 'succ-not-one 'inequalities)

;;; =======================================================================
;;; nn-minus-1-inj:  i /= j and 1 <= i, j  =>  i-1 /= j-1.
;;; Statement: structure-library/order-lemmas.scm:282, unchanged.
;;; Both indices are successors; the monus strips the succ (nn-minus-succ-1),
;;; so equal predecessors put succ back to equal indices.
;;; =======================================================================
(sp (make-wff '(FORALL i (FORALL j (IMPLIES (IN i NN) (IMPLIES (IN j NN)
     (IMPLIES (<= 1 i) (IMPLIES (<= 1 j)
       (IMPLIES (NOT (= i j)) (NOT (= (NN-MINUS i 1) (NN-MINUS j 1))))))))))))
(dk-peel!)
(di)                        ; assume (NN-MINUS i 1) = (NN-MINUS j 1); goal FALSITY
(let ((zi (rkk-pred! 'i))
      (zj (rkk-pred! 'j)))
  (have! (list '= zi zj)
    (lambda ()
      (subst (list '= zi (list 'NN-MINUS 'i 1)))
      (subst (list '= zj (list 'NN-MINUS 'j 1)))
      (ass)))
  (dk-focus-having! (list '= zi zj))
  (fact 'nn-succ-closed zj)
  (have! '(= i j)
    (lambda ()
      (subst (list '= 'i (list 'succ zi)))
      (subst (list '= 'j (list 'succ zj)))
      (subst (list '= zi zj))
      (rfl)))
  (dk-focus-having! '(= i j))
  (ai '(NOT (= i j))))
(rkk-done! 'nn-minus-1-inj)
(topic! 'nn-minus-1-inj 'inequalities)

;;; =======================================================================
;;; succ-in-interval:  q in NN  =>  z in [1,q]  =>  succ z in [1,succ q].
;;; The support (order-lemmas.scm:269) is this statement WITHOUT (IN q NN), and
;;; that form is false -- see the header's countermodel.
;;; =======================================================================
(sp (make-wff '(FORALL q (IMPLIES (IN q NN) (FORALL z
     (IMPLIES (IN z (INTERVAL 1 q)) (IN (succ z) (INTERVAL 1 (succ q)))))))))
(dk-peel!)
(fact 'interval-elt-in-nn 1 'q 'z)
(fact 'interval-lo 1 'q 'z)
(fact 'interval-hi 1 'q 'z)                     ; z <= q
(fact 'nn-succ-closed 'z)
(fact 'nn-succ-closed 'q)
(fact 'nn-one-le-succ 'z)                       ; 1 <= succ z
(fact 'nn-succ-mono 'z 'q)                      ; succ z <= succ q
(fact 'interval-mem-intro 1 '(succ q) '(succ z))
(ass)
(rkk-done! 'succ-in-interval)
(topic! 'succ-in-interval 'inequalities)

;;; =======================================================================
;;; pred-in-interval:  p in NN  =>  i in [1, succ p]  =>  i /= 1
;;;                            =>  NN-MINUS(i,1) in [1,p].
;;; The support (order-lemmas.scm:260) is this statement WITHOUT (IN p NN), and
;;; that form is false -- see the header's countermodel.
;;; i is a successor, succ z = i <= succ p cancels to z <= p, and the monus is
;;; that z.
;;; =======================================================================
(sp (make-wff '(FORALL p (IMPLIES (IN p NN) (FORALL i
     (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
       (IN (NN-MINUS i 1) (INTERVAL 1 p)))))))))
(dk-peel!)
(fact 'nn-succ-closed 'p)
(fact 'interval-elt-in-nn 1 '(succ p) 'i)
(fact 'interval-lo 1 '(succ p) 'i)              ; 1 <= i
(fact 'interval-hi 1 '(succ p) 'i)              ; i <= succ p
(let ((z (rkk-pred! 'i)))
  ;; 1 <= z: z = 0 would make i = succ 0 = 1, which this branch denies.
  (have! (list 'NOT (list '= z 0))
    (lambda ()
      (di)
      (have! '(= 1 (succ 0)) (lambda () (arith)))
      (have! '(= i 1)
        (lambda ()
          (subst (list '= 'i (list 'succ z)))
          (subst (list '= z 0))
          (subst '(= 1 (succ 0)))
          (rfl)))
      (dk-focus-having! '(= i 1))
      (ai '(NOT (= i 1)))))
  (dk-focus-having! (list 'NOT (list '= z 0)))
  (dk-one-le! z)
  (fact 'nn-succ-closed z)
  (have! (list '<= (list 'succ z) '(succ p))
    (lambda () (subst (list '= (list 'succ z) 'i)) (ass)))
  (dk-focus-having! (list '<= (list 'succ z) '(succ p)))
  (fact 'nn-succ-le-cancel z 'p)                ; z <= p
  (fact 'interval-mem-intro 1 'p z)
  (subst (list '= (list 'NN-MINUS 'i 1) z))
  (ass))
(rkk-done! 'pred-in-interval)
(topic! 'pred-in-interval 'inequalities)
