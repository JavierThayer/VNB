;;; test-suite-negative.scm -- the MUST-NOT-PROVE corpus.
;;;
;;; Every check in test-suite.scm asks "does this still work?".  These ask the
;;; opposite question: **is this still REFUSED?**  Each entry is a statement the
;;; system is required to fail on, pushed through the real tactic layer with the
;;; whole library loaded, asserting that the proof state is still OPEN afterwards.
;;;
;;; WHY A SEPARATE CORPUS.  The suite already has ~30 `check-false' refusals, but
;;; they are RULE-level -- "does pi-lambda-type! reject this input", "does
;;; make-wff reject a domainless lambda".  Nothing was THEOREM-level: with the
;;; library loaded, can the tactic layer close a false goal by any route?  So
;;; nothing in the suite would have noticed if a kernel edit reopened the
;;; lambda-domain hole, which until 2026-08-02 proved (IN 0 EMPTY-SET) modulo 0
;;; -- a false theorem with a clean bill.
;;;
;;; THE VACUITY PROBLEM, and the discipline that answers it.  A negative test
;;; that passes because the script wandered off is indistinguishable from one
;;; that passes because the system is sound -- the same trap as a gate that
;;; accepts everything.  So:
;;;
;;;   (1) every entry that can have one carries a PAIRED CONTROL: the same
;;;       tactic, on a true statement, must CLOSE.  A control that stops closing
;;;       means the attack went dead and the negative result is worthless.
;;;   (2) MUTATION at authoring time: break the fix on purpose, watch the entry
;;;       go red, put it back.  Recorded per entry where it was done.
;;;   (3) entries whose historical route can no longer be WRITTEN (make-wff now
;;;       rejects a domainless lambda outright) are labelled DOCUMENTARY: they
;;;       assert the guard fires, not that a live attack failed.
;;;
;;; WHAT THIS ESTABLISHES: that a fixed list of false statements is rejected, and
;;; stays rejected as the code changes.  It is a regression net, NOT a soundness
;;; proof -- it says nothing about the false statements not on the list.
;;;
;;; STATUS 2026-08-06: **LIVE.**  Loaded from the end of test-suite.scm, so its
;;; results land in the SUMMARY.  Helpers it takes from there: check /
;;; check-false / check-proof.  23 checks, all passing.
;;;
;;; THE MUTATION RECORD.  Five guards were deleted on purpose, one at a time, in
;;; a live image (band restart + `set!' of the procedure), and the corpus re-run.
;;; Each turned exactly the entries below red and nothing else:
;;;
;;;   mutation           what was deleted                    entries turned red
;;;   ----------------   ---------------------------------   ------------------
;;;   no-sethood         pi-lambda-type!'s (IN A SET) goal    the ORD entry
;;;   no-domain-match    pi-lambda-type!'s alpha-equiv? on    the FUN(EMPTY-SET,
;;;                        the declared domain                  EMPTY-SET) entry
;;;   no-definedness     pi-reflexivity!'s definedness        pred(0), recip(0)
;;;                        guard (term-self-defined? := #t)
;;;   credulous-arith    arith-eval-formula := true           0=1, 2+2=5, pred(0)
;;;   credulous-ineq     fm-prove := always-infeasible        the false ineq goal
;;;
;;; The runner is scratchpad-local (mnp-mutate.scm); redo it by hand after any
;;; change to the guards it names.  Two of the five mutations found real defects
;;; in the corpus itself on the first pass, which is the whole argument for
;;; doing this: `no-domain-match' turned NOTHING red, because the entry attacked
;;; only the focus leaf and then because the attack could not prove even
;;; (IN EMPTY-SET SET).  A negative test nobody has tried to break is a
;;; negative test that has not been run.
;;;
;;; A FINDING FROM WRITING IT, which is exactly the kind of thing it is for.
;;; Section 2 below tests that the RULE (pi-lambda-type!) refuses a proper-class
;;; domain.  It does.  But `bijection-identity' (bijection.scm) is stated
;;; UNGUARDED -- `forall X. (VNB-LAMBDA x_ X x_) in BIJECTION(X, X)' -- so at
;;; X := ORD it asserts, via bijection-in-fun, that the identity lambdoid on ORD
;;; is in FUN(ORD, ORD), which is precisely what the rule's sethood obligation
;;; exists to prevent.  An AXIOM route around a repaired RULE.  I could not
;;; derive FALSITY from it (the library has no unguarded "the domain of a set
;;; function is a set" -- `dom-of-fun`, theory.scm:499, is guarded on (IN A SET)),
;;; so this is an unsound ASSERTION rather than a demonstrated inconsistency.
;;; The axiom was guarded on (IN X SET) the same day (bijection.scm:148-151), and
;;; `sethood-audit' (audit.scm) is the standing gate for the general shape.

(display "\n--- must-not-prove corpus ---\n")

;;; -----------------------------------------------------------------------
;;; Kit
;;; -----------------------------------------------------------------------

;;; The general attack: normalise, then throw every ground closer at the goal.
;;; Deliberately blunt -- an entry that survives THIS is not surviving a typo.
(define (mnp-attack!)
  (ignore-errors (quietly (lambda () (grind))))
  (ignore-errors (quietly (lambda () (arith))))
  (ignore-errors (quietly (lambda () (crs))))
  ;; A sethood goal is the one shape no driver discharges by hand; dk-set-close!
  ;; (driver-kit.scm) is the library's own answer to it, so the attacker gets it
  ;; too.  Without this the attack could not prove even (IN EMPTY-SET SET), and
  ;; the FUN(EMPTY-SET,EMPTY-SET) entry survived the domain-match mutation on a
  ;; leaf that the real system closes in one line.  dk-set-close! returns #f on
  ;; ORD -- that is the honest boundary (burali-forti), not a weakness.
  (ignore-errors (quietly (lambda ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))
          (dk-set-close! (cadr g)))))))
  (ignore-errors (quietly (lambda () (ass))))
  (ignore-errors (quietly (lambda () (rfl)))))

;;; Attack EVERY open leaf, to exhaustion, not merely the focus.  A tactic that
;;; BRANCHES otherwise buys a refusal for free: `mnp-attack!' closes the leaf it
;;; is looking at, the sibling stays open, and the entry reads "refused" no
;;; matter what the system did.  That is not hypothetical -- it is what the
;;; MUTATION check found on 2026-08-06.  The FUN(EMPTY-SET,EMPTY-SET) entry
;;; below used bare `mnp-attack!'; with pi-lambda-type!'s declared-domain match
;;; deleted on purpose, the rule fired, BOTH its subgoals became provable, and
;;; the entry still passed.  Attacking every leaf is what makes it notice.
(define (mnp-attack-leaves!)
  (let loop ((rounds 3))
    (if (and (> rounds 0) (pair? (proof-leaves)))
        (begin
          (for-each (lambda (l)
                      (ignore-errors (begin (dk-focus! l) (mnp-attack!))))
                    (proof-leaves))
          (loop (- rounds 1))))))

;;; #t when the focus proof is CLOSED.  The corpus asserts this is #f.
(define (mnp-closed?) (null? (proof-open-goals *ps*)))

;;; 1-based context position of a formula, for `ineq' (which cites by index).
(define (mnp-idx form)
  (let loop ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
             (i 1))
    (cond ((null? as) (error "mnp-idx: not in context" form))
          ((equal? (car as) form) i)
          (else (loop (cdr as) (+ i 1))))))

;;; Run an entry with the surface quiet.  The corpus asserts on ONE bit -- did
;;; the proof close -- so the running commentary of a hundred `show' dumps is
;;; noise in a suite whose signal is its SUMMARY line.  Note the usual hazard
;;; (`quietly' silences vnb-guard, so an erroring tactic becomes a silent
;;; no-op): here it is harmless for a refusal, and for a CONTROL the closure
;;; assertion is exactly the check that the script did not silently die.
(define (mnp-run-entry goal thunk)
  (quietly (lambda ()
    (sp (make-wff goal))
    (ignore-errors (thunk))
    (mnp-closed?))))

;;; (mnp-refuses LABEL GOAL THUNK) -- run THUNK at GOAL, require it stays open.
(define (mnp-refuses label goal thunk)
  (check (string-append "must NOT prove: " label)
         (lambda () (mnp-run-entry goal thunk))
         #f))

;;; (mnp-control LABEL GOAL THUNK) -- the same machinery must CLOSE this one.
(define (mnp-control label goal thunk)
  (check (string-append "  control (must close): " label)
         (lambda () (mnp-run-entry goal thunk))
         #t))

;;; -----------------------------------------------------------------------
;;; 1.  PARTIALITY.  `=' is partial, so t = t is a DEFINEDNESS claim and `rfl'
;;;     must refuse it for a term that is not defined.  pred(0) is the sharpest
;;;     case in the library: nn-pred.scm defines pred by a description that is
;;;     empty at 0 (no natural has successor 0), on purpose.
;;; -----------------------------------------------------------------------

(mnp-refuses "(pred 0) = (pred 0) -- pred is undefined at 0"
  '(= (PRED 0) (PRED 0))
  (lambda () (ignore-errors (fact 'pred-in-nn 0)) (mnp-attack!)))

(mnp-control "pred(n) = pred(n) WITH the definedness witness"
  '(FORALL n_ (IMPLIES (IN n_ NN) (IMPLIES (NOT (= n_ 0)) (= (PRED n_) (PRED n_)))))
  (lambda () (di) (di) (fact 'pred-in-nn 'n_) (rfl)))

(mnp-refuses "(recip 0) = (recip 0) -- the reciprocal is undefined at 0"
  '(= (recip 0) (recip 0))
  (lambda () (mnp-attack!)))

;;; -----------------------------------------------------------------------
;;; 2.  THE LAMBDA-DOMAIN HOLE (unsound until 2026-08-02, TWO ways).
;;;
;;;   (a) the term did not declare its domain, so (VNB-LAMBDA x x) typed into
;;;       FUN(A,A) for EVERY A; with A = NN and A = EMPTY-SET,
;;;       fun-domain-apply-def then gave (IN 0 EMPTY-SET) modulo 0.
;;;   (b) no sethood obligation, so (VNB-LAMBDA x ORD x) went into FUN(ORD,ORD)
;;;       with ORD a proper class.
;;; -----------------------------------------------------------------------

;;; (a) is now DOCUMENTARY at the term level -- the old term cannot be written.
(check "must NOT parse: a DOMAINLESS VNB-LAMBDA [documentary: the 2026-08-02 repair]"
  (lambda ()
    (quietly (lambda ()
      (condition? (ignore-errors (make-wff '(IN (VNB-LAMBDA x x) (FUN NN NN))))))))
  #t)

;;; ... and live at the goal level: a declared domain that is not the FUN's.
;;; MUTATION-CHECKED 2026-08-06: deleting the `alpha-equiv?' domain match in
;;; pi-lambda-type! turns this entry red -- but only since it began attacking
;;; every leaf (see mnp-attack-leaves! above); with bare `mnp-attack!' it stayed
;;; green under the mutation, which is the vacuity this corpus exists to avoid.
(mnp-refuses "lam x in NN. x  is in FUN(EMPTY-SET, EMPTY-SET)"
  '(IN (VNB-LAMBDA x NN x) (FUN EMPTY-SET EMPTY-SET))
  (lambda () (ignore-errors (lam-t)) (mnp-attack-leaves!)))

;;; ... and the false theorem the hole produced.
(mnp-refuses "0 in EMPTY-SET"
  '(IN 0 EMPTY-SET)
  (lambda () (mnp-attack!)))

;;; (b) the sethood half: lam-t FIRES here, and must leave (IN ORD SET) owed --
;;;     which is not closable, ORD being a proper class (burali-forti).
;;;     MUTATION-CHECKED 2026-08-06: deleting the (IN A SET) subgoal from
;;;     pi-lambda-type! turns this entry red.
(mnp-refuses "lam x in ORD. x  is in FUN(ORD, ORD) -- proper-class domain"
  '(IN (VNB-LAMBDA x ORD x) (FUN ORD ORD))
  (lambda () (ignore-errors (lam-t)) (mnp-attack-leaves!)))

(mnp-control "lam x in NN. x  IS in FUN(NN, NN)"
  '(IN (VNB-LAMBDA x NN x) (FUN NN NN))
  (lambda ()
    (lam-t)
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) '(IN NN SET))
                    (begin (fact 'nn-is-set) (ass))
                    (begin (di) (ass))))
              (proof-leaves))))

;;; -----------------------------------------------------------------------
;;; 3.  GROUND ARITHMETIC.  `arith' is a trusted ORACLE: it closes by
;;;     computation and leaves no leaf, so what it DECLINES is part of the
;;;     trusted boundary and belongs here.
;;; -----------------------------------------------------------------------

(mnp-refuses "0 = 1" '(= 0 1) (lambda () (mnp-attack!)))
(mnp-refuses "2 + 2 = 5" '(= (+ 2 2) 5) (lambda () (mnp-attack!)))
(mnp-control "2 + 2 = 4" '(= (+ 2 2) 4) (lambda () (arith)))

;;; -----------------------------------------------------------------------
;;; 4.  THE ineq ORACLE'S BOUNDARY.  Two different failures: a goal that is
;;;     FALSE (unsoundness if it ever closed) and a goal that is TRUE but
;;;     nonlinear (scope -- ineq linearises, so it must decline).
;;; -----------------------------------------------------------------------

(mnp-refuses "a <= b  |-  b < a   [false: ineq must decline]"
  '(FORALL a_ (IMPLIES (IN a_ RR) (FORALL b_ (IMPLIES (IN b_ RR)
     (IMPLIES (<= a_ b_) (< b_ a_))))))
  (lambda () (di) (di) (ignore-errors (ineq (mnp-idx '(<= a_ b_)))) (mnp-attack!)))

(mnp-refuses "0 <= a  |-  0 <= a*a   [TRUE but nonlinear: ineq must decline]"
  '(FORALL a_ (IMPLIES (IN a_ RR) (IMPLIES (<= 0 a_) (<= 0 (* a_ a_)))))
  (lambda () (di) (di) (ignore-errors (ineq (mnp-idx '(<= 0 a_))))))

(mnp-control "a <= b, b <= c  |-  a <= c   [ineq's own job]"
  '(FORALL a_ (IMPLIES (IN a_ RR) (FORALL b_ (IMPLIES (IN b_ RR)
     (FORALL c_ (IMPLIES (IN c_ RR)
       (IMPLIES (<= a_ b_) (IMPLIES (<= b_ c_) (<= a_ c_)))))))))
  (lambda () (di) (di) (di) (ineq (mnp-idx '(<= a_ b_)) (mnp-idx '(<= b_ c_)))))

;;; -----------------------------------------------------------------------
;;; 5.  TODAY'S WORK, spot-checked for consistency.  We proved that nothing
;;;     injects S(1) into S(0); the POSITIVE had therefore better not also be
;;;     provable.  If both ever pass, the library is inconsistent and this pair
;;;     is where it shows.
;;; -----------------------------------------------------------------------

(mnp-refuses "f is an injection S(1) -> S(0)"
  '(IN f_ (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))
  (lambda () (mnp-attack!)))

(mnp-control "NO f is an injection S(1) -> S(0)  [the theorem]"
  '(FORALL f_ (NOT (IN f_ (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))))
  (lambda () (fact 'no-injection-seg-1-into-seg-0) (ass)))

;;; -----------------------------------------------------------------------
;;; 6.  CARDINALITY.  CARD(A) is an ORDINAL; finiteness is an extra hypothesis
;;;     every card-* fact carries.  A proof that forgot it would land here.
;;; -----------------------------------------------------------------------

(mnp-refuses "every set has a NATURAL cardinal"
  '(FORALL a_ (IMPLIES (IN a_ SET) (IN (CARD a_) NN)))
  (lambda () (di) (ignore-errors (fact 'card-in-ord 'a_)) (mnp-attack!)))

(mnp-control "every set has an ORDINAL cardinal  [card-in-ord]"
  '(FORALL a_ (IMPLIES (IN a_ SET) (IN (CARD a_) ORD)))
  (lambda () (di) (fact 'card-in-ord 'a_) (ass)))

;;; -----------------------------------------------------------------------
;;; 7.  THE TWO SILENT-WRONG-ANSWER BUGS.  Neither produced a FALSE theorem, so
;;;     neither can be caught by asking whether a goal closes: each made the
;;;     machine prove a DIFFERENT statement from the one on the screen.  The
;;;     assertion is therefore about the term the walker returns, not about the
;;;     proof state.  They belong in this corpus all the same -- "the system
;;;     must not silently answer a question you did not ask" is the same kind of
;;;     obligation as "the system must not prove a falsehood".
;;; -----------------------------------------------------------------------

;;; (a) SIMULTANEOUS SUBSTITUTION (the macete rewriter, unsound until
;;;     2026-07-11).  `apply-subst' folded `subst-free' over the bindings, so
;;;     whatever an earlier binding substituted IN was visible to every later
;;;     one.  The fixture is the historical one: SPANS has parameters
;;;     (md n u sm), and the caller's term for `sm' contains the caller's own
;;;     `n' and `u' -- which is what happens the moment a recursive
;;;     construction is fed back into its own definition.
;;;
;;;     NOT a duplicate of test-suite.scm:4363 / 4372, and the difference is the
;;;     point.  Both of those list `sm' LAST, and with that order the naive fold
;;;     substitutes the offending term in after `n' and `u' have already been
;;;     consumed -- so it returns the SAME answer as subst-free*.  Measured
;;;     2026-08-06: for both fixtures, fold and simultaneous agree exactly.  Two
;;;     checks written against a specific bug that the bug itself cannot fail.
;;;     Listing `sm' FIRST is what makes the distinction observable, and the
;;;     control below pins the fold's wrong answer so it stays observable.
(define mnp-spans-bindings
  '((sm . (INTERSECTION sm (SPAN md n (BLOCK u n 1)))) (n . k) (u . w)))

(check "must NOT rewrite: apply-subst is simultaneous, not a fold [2026-07-11]"
  (lambda () (apply-subst mnp-spans-bindings '(SPANS md n u sm)))
  '(SPANS md k w (INTERSECTION sm (SPAN md n (BLOCK u n 1)))))

;;; ... and it must not depend on the order the bindings arrive in.
(check "must NOT rewrite: apply-subst is order-independent [2026-07-11]"
  (lambda () (equal? (apply-subst mnp-spans-bindings '(SPANS md n u sm))
                     (apply-subst (reverse mnp-spans-bindings) '(SPANS md n u sm))))
  #t)

;;; The anti-vacuity control, and the shape of the old bug in one line: the
;;; fold gives a DIFFERENT term, so the two checks above are not asserting a
;;; distinction the code could not fail to make.
(check "  control: the naive fold really does give a different term"
  (lambda ()
    (fold-left (lambda (e b) (subst-free (car b) (cdr b) e))
               '(SPANS md n u sm) mnp-spans-bindings))
  '(SPANS md k w (INTERSECTION sm (SPAN md k (BLOCK w k 1)))))

;;; (b) NTH's INDEX invisible to the walkers (fixed 2026-08-04).  `(NTH k e)'
;;;     is 1-indexed with the index FIRST; it used to have a special case that
;;;     skipped that position, so a bound index was neither reported free nor
;;;     substituted into -- and `nth-in-range' could not be stated.
(check "must NOT hide: NTH's index is a free-variable position [2026-08-04]"
  (lambda () (and (memq 'i (free-vars '(NTH i m))) #t))
  #t)

(check "must NOT hide: NTH's index is a substitution position [2026-08-04]"
  (lambda () (subst-free 'i 3 '(NTH i m)))
  '(NTH 3 m))

;;; -----------------------------------------------------------------------
;;; NOT YET COVERED, and why -- so the gaps are visible rather than implied.
;;;
;;; * An ADVERSARIAL attacker.  `mnp-attack!' is a fixed blunt script -- grind,
;;;   arith, crs, the sethood closer, ass, rfl -- run at every open leaf.  For
;;;   the sharper entries it should be a `scout' search, so that an entry means
;;;   "no route the system's own search finds" rather than "this script did
;;;   not".  The mutation record above is what currently stands in for it: an
;;;   entry no mutation can turn red is an entry whose attack may be too weak.
;;; * Two entries are CONSISTENCY CANARIES rather than fix-regressions, and no
;;;   mutation of a single guard turns them red: `0 in EMPTY-SET' (the false
;;;   theorem the lambda-domain hole actually produced -- reaching it needs a
;;;   two-domain derivation through fun-domain-apply-def, which the blunt attack
;;;   does not construct) and `f is an injection S(1) -> S(0)' (paired with the
;;;   theorem that nothing is; if both ever pass, the library is inconsistent).
;;;   They are cheap and they are worth keeping, but they are watching for a
;;;   collapse, not guarding a specific repair.
;;; * The `0 <= a |- 0 <= a*a' entry guards the LINEARIZER, not Fourier-Motzkin:
;;;   `formula->lin+rel' refuses the nonlinear goal before `fm-prove' is ever
;;;   called, which is why the credulous-ineq mutation leaves it green.
;;; -----------------------------------------------------------------------
