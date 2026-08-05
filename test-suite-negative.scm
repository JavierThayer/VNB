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
;;; STATUS 2026-08-05: **DRAFT -- NOT WIRED IN AND NOT YET RUN.**  Nothing loads
;;; this file; test-suite.scm does not mention it.  Next session: run it against
;;; the band, fix the entries that misbehave, do the mutation checks, then load
;;; it from the end of test-suite.scm so its results land in the SUMMARY.
;;; Helpers it expects from there: check / check-false / check-proof.
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
;;; The axiom is being guarded on (IN X SET) the same day.

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
  (ignore-errors (quietly (lambda () (ass))))
  (ignore-errors (quietly (lambda () (rfl)))))

;;; #t when the focus proof is CLOSED.  The corpus asserts this is #f.
(define (mnp-closed?) (null? (proof-open-goals *ps*)))

;;; 1-based context position of a formula, for `ineq' (which cites by index).
(define (mnp-idx form)
  (let loop ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
             (i 1))
    (cond ((null? as) (error "mnp-idx: not in context" form))
          ((equal? (car as) form) i)
          (else (loop (cdr as) (+ i 1))))))

;;; (mnp-refuses LABEL GOAL THUNK) -- run THUNK at GOAL, require it stays open.
(define (mnp-refuses label goal thunk)
  (check (string-append "must NOT prove: " label)
         (lambda () (sp (make-wff goal)) (ignore-errors (thunk)) (mnp-closed?))
         #f))

;;; (mnp-control LABEL GOAL THUNK) -- the same machinery must CLOSE this one.
(define (mnp-control label goal thunk)
  (check (string-append "  control (must close): " label)
         (lambda () (sp (make-wff goal)) (ignore-errors (thunk)) (mnp-closed?))
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
  (lambda () (condition? (ignore-errors (make-wff '(IN (VNB-LAMBDA x x) (FUN NN NN))))))
  #t)

;;; ... and live at the goal level: a declared domain that is not the FUN's.
(mnp-refuses "lam x in NN. x  is in FUN(EMPTY-SET, EMPTY-SET)"
  '(IN (VNB-LAMBDA x NN x) (FUN EMPTY-SET EMPTY-SET))
  (lambda () (ignore-errors (lam-t)) (mnp-attack!)))

;;; ... and the false theorem the hole produced.
(mnp-refuses "0 in EMPTY-SET"
  '(IN 0 EMPTY-SET)
  (lambda () (mnp-attack!)))

;;; (b) the sethood half: lam-t FIRES here, and must leave (IN ORD SET) owed --
;;;     which is not closable, ORD being a proper class (burali-forti).
(mnp-refuses "lam x in ORD. x  is in FUN(ORD, ORD) -- proper-class domain"
  '(IN (VNB-LAMBDA x ORD x) (FUN ORD ORD))
  (lambda ()
    (ignore-errors (lam-t))
    (for-each (lambda (l) (dk-focus! l) (mnp-attack!)) (proof-leaves))))

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
;;; NOT YET COVERED, and why -- so the gaps are visible rather than implied.
;;;
;;; * The macete SIMULTANEOUS-SUBSTITUTION bug (2026-07-11): it produced a
;;;   DIFFERENT theorem rather than an obviously false one, so the entry needs a
;;;   bespoke fixture -- a definition whose parameters reappear inside the term
;;;   matched to a later parameter -- and an assertion about the REWRITTEN FORM,
;;;   not about closure.  Wanted; not written.
;;; * NTH's index invisible to the walkers (fixed 2026-08-04): same shape, a
;;;   subst-free/free-vars unit check rather than a closure check.
;;; * An ADVERSARIAL attacker.  `mnp-attack!' is a fixed blunt script; for the
;;;   sharper entries it should be a `scout' search, so an entry means "no route
;;;   the system's own search finds" rather than "this script did not".
;;; -----------------------------------------------------------------------
