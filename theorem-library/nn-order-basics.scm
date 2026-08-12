;;; nn-order-basics.scm -- the elementary NN order facts, PROVEN.
;;;
;;; These three were PSS supports in structure-library/order-lemmas.scm, and two
;;; of them carried the TOP warrant tier, `proof', while naming no machine proof
;;; -- `nn-le-refl' ("nn-in-rr; rr-leq-reflexive") and `nn-pair-upper-bound'
;;; ("take c = a + b, or max(a,b)").  Both warrants described a derivation
;;; nobody had run.  The `warrant-invariant' gate cannot catch that class: it
;;; excludes PSS supports by construction (load.scm), so a support may claim
;;; `proof' indefinitely.
;;;
;;; They are cheap, and at the elementary level an assertion costs more than it
;;; saves: a reader who checks the base of the library first finds "m <= m + n"
;;; taken on faith and stops trusting what is built on it.
;;;
;;; Loads after interactive/proof-debt (sp/di/mac/fact/qed) and driver-kit
;;; (use-induction), and BEFORE the earliest consumers -- theorem-library/
;;; nn-order-proof (nn-le-refl) and theorem-library/coord-block-estimate-proof
;;; (nn-pair-upper-bound).

;; ---- file-local helpers (nb- prefix; never named like a tactic) -----------
;; Both exist ONLY because `fact' will not split a conjunctive antecedent, and
;; nn-add-closed states its hypotheses as (AND (IN a NN) (IN b NN)).  If that
;; axiom is ever restated as nested implications -- the way rr-sup-in is, which
;; is why THAT one needs no helper -- both of these disappear.
(define (nb-focus-exact form)
  (let loop ((l (proof-leaves)))
    (cond ((null? l) (error "nb-focus-exact: no leaf with goal" form))
          ((equal? (wff-formula (sequent-node-assertion (car l))) form)
           (dk-focus! (car l)))
          (else (loop (cdr l))))))

(define (nb-have-and a b)
  (have! (list 'AND a b)
         (lambda () (di) (ass) (nb-focus-exact b) (ass))))

(define (nb-fact-and lemma args a b)
  (let ((land (dk-landed* (lambda () (apply fact (cons lemma args))))))
    (nb-have-and a b)
    (detach! (car land))))

;;; ----------------------------------------------------------------------
;;; nn-in-rr:  a natural number is a real.
;;; Its old warrant, like nn-le-refl's, WAS the derivation -- "the inclusion
;;; chain NN subset ZZ subset QQ subset RR composed" -- and it too claimed the
;;; `proof' tier while naming no machine proof.  Three citations, one per link;
;;; all three inclusions are axioms in number-systems.scm.
;;; Proved FIRST in this file because nn-le-refl below cites it.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (IN k RR)))))
(di)
(fact 'nn-subset-zz 'k)
(fact 'zz-subset-qq 'k)
(fact 'qq-subset-rr 'k)
(ass)
(qed 'nn-in-rr)
(topic! 'nn-in-rr 'plumbing)


;;; ----------------------------------------------------------------------
;;; TRANSITIVITY, three statements, all from the PRIMITIVE rr-leq-transitive
;;; (number-systems.scm) -- which is guarded on (IN a RR) and takes its two
;;; inequalities as one AND.
;;;
;;; nn-le-trans is the one that changed CONTENT.  It used to be stated with no
;;; guards at all -- `forall a b c. a<=b => b<=c => a<=c' -- which is strictly
;;; stronger than anything the axioms license: no axiom constrains `<=' off the
;;; numeric chain, so the unguarded form is an assumption about the order
;;; relation on arbitrary objects.  Consistent (read `<=' as the real order and
;;; nothing else and it holds vacuously off RR), but unlicensed, and doing work
;;; the guarded version does honestly.  The library's own trusted oracle takes
;;; the opposite line: `ineq' refuses to certify an atom without a literal
;;; (IN t RR) and does no subtype reasoning, so Farkas demands typing for every
;;; atom while that axiom handed out transitivity with none.
;;;
;;; The name was the disguise: despite the `nn-' prefix the old statement
;;; mentioned NN nowhere, so a reader scanning the support list saw a fact about
;;; naturals and got a fact about everything.  It is now genuinely about NN.
(define (nb-and3 a b c)
  (have! (list 'AND a (list 'AND b c))
         (lambda () (di) (ass) (nb-focus-exact (list 'AND b c))
                    (di) (ass) (nb-focus-exact c) (ass))))
(define (nb-and2 a b)
  (have! (list 'AND a b) (lambda () (di) (ass) (nb-focus-exact b) (ass))))

;; rr-le-trans -- AND-antecedent form
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (AND (<= x y) (<= y z)) (<= x z)))))))))) 
(di) (di) (di) (di)
(nb-and3 '(IN x RR) '(IN y RR) '(IN z RR))
(fact 'rr-leq-transitive 'x 'y 'z)
(ass)
(qed 'rr-le-trans)
(topic! 'rr-le-trans 'inequalities)

;; rr-le-trans-c -- curried, so `fact' discharges each guard from context
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL z (IMPLIES (IN z RR)
       (IMPLIES (<= x y) (IMPLIES (<= y z) (<= x z))))))))))) 
(di) (di) (di) (di) (di)
(nb-and3 '(IN x RR) '(IN y RR) '(IN z RR))
(nb-and2 '(<= x y) '(<= y z))
(fact 'rr-leq-transitive 'x 'y 'z)
(ass)
(qed 'rr-le-trans-c)
(topic! 'rr-le-trans-c 'inequalities)

;; nn-le-trans-guarded -- transitivity GUARDED on NN.  This is what nn-le-trans
;; SHOULD be; it is parked under its own name because the migration is
;; incomplete, see the note in structure-library/order-lemmas.scm.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN) (FORALL b_ (IMPLIES (IN b_ NN)
     (FORALL c_ (IMPLIES (IN c_ NN)
       (IMPLIES (<= a_ b_) (IMPLIES (<= b_ c_) (<= a_ c_)))))))))))
(di) (di) (di) (di) (di)
(fact 'nn-in-rr 'a_)
(fact 'nn-in-rr 'b_)
(fact 'nn-in-rr 'c_)
(nb-and3 '(IN a_ RR) '(IN b_ RR) '(IN c_ RR))
(nb-and2 '(<= a_ b_) '(<= b_ c_))
(fact 'rr-leq-transitive 'a_ 'b_ 'c_)
(ass)
(qed 'nn-le-trans-guarded)
(topic! 'nn-le-trans-guarded 'inequalities)

;;; ----------------------------------------------------------------------
;;; nn-le-refl:  k <= k on NN.
;;; Its old warrant WAS the proof: NN sits in RR (nn-in-rr) and <= is reflexive
;;; there (rr-leq-reflexive, an axiom).  Two citations.
(sp (make-wff (forall-guarded 'k '(IN k NN) '(<= k k))))
(di)
(fact 'nn-in-rr 'k)
(fact 'rr-leq-reflexive 'k)
(ass)
(qed 'nn-le-refl)
(topic! 'nn-le-refl 'inequalities)

;;; ----------------------------------------------------------------------
;;; nn-le-add-right:  m <= m + n.
;;;
;;; Induction on n, NOT on m, and the asymmetry is real: the recursion equation
;;; nn-add-succ is stated on the SECOND argument (a + succ b = succ(a + b)), so
;;; induction on n uses it directly.  Inducting on m would need
;;; succ m + n = succ(m + n), which is not an axiom -- recoverable through
;;; nn-add-comm twice, but two steps longer for nothing.
;;;
;;; The induction variable is stated OUTERMOST because `di' is greedy: it takes
;;; the whole leading FORALL/IMPLIES prefix, so peeling "just m" is not
;;; available, and use-induction requires the goal to be (forall v ...).
(sp (make-wff (forall-guarded 'n '(IN n NN)
                (forall-guarded 'm '(IN m NN) '(<= m (+ m n))))))
(define nb-frame (use-induction))

;; base:  m <= m + 0.  nn-add-zero rewrites m + 0 to m; then reflexivity.
(dk-focus! (cdr (assq 'base nb-frame)))
(di)
(mac 'nn-add-zero)
(fact 'nn-le-refl 'm)
(ass)

;; step:  IH (m <= m + n)  |-  m <= m + succ n.
;; nn-add-succ turns the goal into m <= succ(m + n); the IH gives m <= m + n and
;; nn-le-succ gives m + n <= succ(m + n), so transitivity closes it.  The typing
;; (IN (+ m n) NN) is needed by nn-le-succ and is what nb-fact-and assembles.
(dk-focus! (cdr (assq 'step nb-frame)))
(di)
(mac 'nn-add-succ)
(inst+ (cdr (assq 'ih nb-frame)) 'm)
(nb-fact-and 'nn-add-closed '(m n) '(IN m NN) '(IN n NN))
(fact 'nn-le-succ '(+ m n))
;; nn-le-trans is GUARDED on NN (see above), so succ(m+n) must be typed too --
;; this proof used to chain through it without ever saying it was a natural,
;; which is precisely the unlicensed strength the old unguarded statement gave.
(fact 'nn-succ-closed '(+ m n))
(fact 'nn-le-trans-guarded 'm '(+ m n) '(succ (+ m n)))
(ass)
(qed 'nn-le-add-right)
(topic! 'nn-le-add-right 'inequalities)

;;; ----------------------------------------------------------------------
;;; nn-pair-upper-bound:  NN is directed -- any two naturals have a common
;;; upper bound.  Take c = a + b: one half is nn-le-add-right outright, the
;;; other is nn-le-add-right at the swapped arguments plus commutativity.
(sp (make-wff (forall-guarded '(a b) (list '(IN a NN) '(IN b NN))
                (forsome-guarded 'c '(IN c NN)
                  (conjuncts->and (list '(<= a c) '(<= b c)))))))
(di) (di) (di)
(ew '(+ a b))
(di)
;; c in NN
(nb-fact-and 'nn-add-closed '(a b) '(IN a NN) '(IN b NN))
(ass)
;; The second conjunct is itself an AND (di splits one level at a time).
(nb-focus-exact '(AND (<= a (+ a b)) (<= b (+ a b))))
(di)
;; a <= a + b  -- nn-le-add-right at n := b, m := a
(nb-focus-exact '(<= a (+ a b)))
(fact 'nn-le-add-right 'b 'a)
(ass)
;; b <= a + b  -- nn-le-add-right at n := a, m := b gives b <= b + a; commute.
(nb-focus-exact '(<= b (+ a b)))
(mac 'nn-add-comm)
(fact 'nn-le-add-right 'a 'b)
(ass)
(qed 'nn-pair-upper-bound)
(topic! 'nn-pair-upper-bound 'inequalities)
