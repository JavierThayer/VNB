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
;;; Each turned exactly the entries below red and nothing else.  A SIXTH was added
;;; 2026-08-13 -- the (IN x SET) conjunct of make-set-membership -- and that one
;;; was not a drill: the axiom really was unguarded, and section 2b's two entries
;;; both close against it (mutation run: scratchpad/mnp-makeset-entry-probe.scm,
;;; #t #t against the mutant, #f #f against the repair, control green both ways).
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
;;; The runner is `./mutation-check' (mutation-check.scm), which installs each
;;; mutant in a fresh image, re-runs this file, and FAILS if a predicted entry
;;; stays green -- so the table above is a command, not a comment.  It costs
;;; about a second and wants a current band.
;;;
;;; Two of the five mutations found real defects
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
;;; 2b.  THE MAKE-SET CLASS LEAK (unsound until 2026-08-13).
;;;
;;; `{a, b}' is surface sugar for (MAKE-SET (LIST a b)), and make-set-membership
;;; was stated as an UNCONDITIONAL iff -- unlike its neighbours pairing-membership
;;; and power-set-membership, both of which carry a sethood conjunct precisely so
;;; that the iff plus membership-implies-sethood cannot force a class into SET.
;;; MAKE-SET had been missed.  The attack is eight lines and bills nothing:
;;;
;;;   x := ORD, L := (LIST ORD ORD), witness i := 1
;;;   len-r / nth-r reduce the literal spine     (sound, and unguarded)
;;;   (= ORD ORD) closes by rfl                  (ORD is term-self-defined?)
;;;   => ORD in make-set(...)  => (membership-implies-sethood)  ORD in SET
;;;
;;; against burali-forti.  MUTATION-CHECKED 2026-08-13 BY CONSTRUCTION: this
;;; entry is red on the axiom as it stood -- the probe that proved it is
;;; scratchpad/makeset-class-probe.scm -- and green with the (IN x SET)
;;; conjunct in place.  The control below shows the attack is still live: the
;;; same route on a genuine set must CLOSE.
;;; -----------------------------------------------------------------------

(define (mnp-makeset-route!)
  (mac 'make-set-membership)
  (mnp-attack-leaves!)
  (ignore-errors
   (begin
     (ew 1)
     (len-r)
     (nth-r)
     (mnp-attack-leaves!))))

(mnp-refuses "ORD in {ORD, ORD} -- a proper class is a member of nothing"
  '(IN ORD (MAKE-SET (LIST ORD ORD)))
  (lambda () (mnp-makeset-route!)))

;;; The payoff, driven leaf by leaf.  NOT written with `have!': it ERRORS when
;;; its side goal stays open, and MIT's `ignore-errors' does not trap a plain
;;; (error ...) -- the entry aborted the whole suite run before this was
;;; rewritten.  Every command below WARNS on failure instead.  The route is the
;;; probe's, step for step: cut the membership, drive the make-set iff on the
;;; side goal, then membership-implies-sethood on the main branch.
(mnp-refuses "ORD in SET, by way of {ORD, ORD}"
  '(IN ORD SET)
  (lambda ()
    (cut '(IN ORD (MAKE-SET (LIST ORD ORD))))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) '(IN ORD (MAKE-SET (LIST ORD ORD))))
                    (mnp-makeset-route!)))
              (proof-leaves))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) '(IN ORD SET))
                    (begin
                      (fact 'membership-implies-sethood 'ORD '(MAKE-SET (LIST ORD ORD)))
                      (ass))))
              (proof-leaves))
    (mnp-attack-leaves!)))

;;; The control has to close under the MUTATION too, or a mutation run cannot
;;; tell "the guard is gone" from "the attack went dead".  Under the mutation
;;; the iff's RHS has no (IN x SET) conjunct, so the `di' split yields nothing
;;; and the single leaf IS the existential -- hence the fallback to
;;; (proof-leaves) rather than a fixed two-branch shape.
(mnp-control "0 IS in {0, 1} -- the same route, on a set"
  '(IN 0 (MAKE-SET (LIST 0 1)))
  (lambda ()
    (mac 'make-set-membership)
    (let ((opened (dk-opened (lambda () (di)))))
      (for-each
       (lambda (l)
         (dk-focus! l)
         (if (equal? (dk-goal) '(IN 0 SET))
             (begin (fact 'nn-zero-in) (fact 'membership-implies-sethood 0 'NN) (ass))
             (begin (ew 1) (len-r) (nth-r) (mnp-attack-leaves!))))
       (if (null? opened) (proof-leaves) opened)))))

;;; -----------------------------------------------------------------------
;;; 2c.  AN UNSATISFIABLE STRUCTURE PREDICATE (defective until 2026-08-23).
;;;
;;; A structure predicate that CONTRADICTS ITSELF is the quietest unsoundness
;;; in the tree: it proves no false theorem of its own, it makes every theorem
;;; carrying it as a hypothesis VACUOUSLY true, and from inside any such proof
;;; a vacuous hypothesis and a satisfiable one are indistinguishable.  The
;;; whole library loads, every bill reads the same, and nothing says a word.
;;;
;;; NORMED-VECTOR-SPACE was in exactly that state.  Two halves of one
;;; declaration, fourteen lines apart (normed-vector-space.scm):
;;;
;;;     (substructure SCAL RING)    -> the conjunct (IS-RING (SCAL s)), and
;;;                                    IS-RING pins length(scal(s)) = 6
;;;     (law "scal(s) = rr-normed-field")
;;;                                 -> and RR-NORMED-FIELD is the SEVEN-tuple
;;;                                    [RR binplus bintimes binneg 0 1 abs]
;;;
;;; Six against seven, so IS-NORMED-VECTOR-SPACE(s) |- falsity, in four moves:
;;; unfold the predicate, unfold IS-RING, compute the tuple's length from the
;;; pinning law, and let `arith' refute the pair.  hahn-banach, norm-as-sup,
;;; vector-taylor, dual-space and directional-derivative were all vacuous on it.
;;; The repair pins the scalars through the RING VIEW of the normed field --
;;; NORMED-FIELD-AS-COMMUTATIVE-RING (views.scm:167), which projects slots 1..6
;;; into a fresh 6-tuple -- and 6 = 6.
;;;
;;; MUTATION-CHECKED 2026-08-23 BY CONSTRUCTION: this entry is RED against the
;;; declaration as it stood (the probe is scratchpad/nvs-falsity-probe.scm,
;;; which measures both length claims and reports DEFECT CONFIRMED / DEFECT
;;; GONE) and green against the repair.  The control below is what keeps that
;;; meaningful: the SAME arithmetic route, on a genuine length mismatch, must
;;; still CLOSE -- so a green entry here says the structure changed, not that
;;; the attack went dead.
;;; -----------------------------------------------------------------------

;;; Unfold IS-NORMED-VECTOR-SPACE and its IS-RING conjunct down to atoms.
(define (mnp-nvs-unfold!)
  (di)
  (mac-h 'IS-NORMED-VECTOR-SPACE '(IS-NORMED-VECTOR-SPACE s))
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 60)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n))))
  (vnb-guard (lambda () (mac-h 'IS-RING '(IS-RING (SCAL s)))))
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 60)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND)) (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; The pinning law as it stands in the context: (= (SCAL s) <the scalar tuple>).
(define (mnp-nvs-pinning)
  (let loop ((l (dk-asms)))
    (cond ((null? l) #f)
          ((and (pair? (car l)) (eq? (caar l) '=) (equal? (cadr (car l)) '(SCAL s)))
           (car l))
          (else (loop (cdr l))))))

;;; length(T) = K, computed from the pinning law alone: substitute the pinned
;;; tuple in, unfold whatever constructs it, and reduce the LIST literal.
(define (mnp-nvs-length-claim! pin term k)
  (have! (list '= (list 'LENGTH term) k)
         (lambda ()
           (subst pin)
           (mac 'NORMED-FIELD-AS-COMMUTATIVE-RING)   ; a no-op before the repair
           (mac 'rr-normed-field-def)
           (len-r)
           (arith))))

;;; The attack.  The NOT goes in FIRST: `arith' rewrites the goal with the
;;; context equation length(scal(s)) = 6 that IS-RING supplies, and landing the
;;; other length equation first would let it rewrite with THAT one instead and
;;; decide nothing.
(mnp-refuses "IS-NORMED-VECTOR-SPACE(s) |- falsity -- the predicate must be SATISFIABLE"
  '(IMPLIES (IS-NORMED-VECTOR-SPACE s) FALSITY)
  (lambda ()
    (mnp-nvs-unfold!)
    ;; `vnb-guard', NOT `ignore-errors': measured on this MIT build, 2026-08-23,
    ;; (ignore-errors (error "boom")) drops into the error REPL -- it catches
    ;; nothing.  The other `ignore-errors' calls in this file have never been
    ;; exercised (a tactic guards itself and RETURNS a <vnb-error>), but `have!'
    ;; raises a bare Scheme `error' when its thunk leaves the side goal open,
    ;; which is exactly what happens here once the structure is repaired.
    (vnb-guard
      (lambda ()
        (have! '(NOT (= (LENGTH (SCAL s)) 7)) (lambda () (arith)))
        (mnp-nvs-length-claim! (mnp-nvs-pinning) '(SCAL s) 7)
        (ai '(NOT (= (LENGTH (SCAL s)) 7)))))
    (mnp-attack-leaves!)))

;;; ANTI-VACUITY, and it is the whole reason the entry above means anything.
;;; The refusal must be the STRUCTURE's doing, not the attack's -- so here is
;;; the SAME derivation, move for move, against the defective pinning written
;;; out by hand as a hypothesis.  It must CLOSE.  If it stops closing, the
;;; entry above has gone vacuous and is asserting nothing.
(mnp-control "the 6-against-7 derivation is LIVE (the old pinning, by hand)"
  '(IMPLIES (AND (= (LENGTH z) 6) (= z RR-NORMED-FIELD)) FALSITY)
  (lambda ()
    (di)
    (ai '(AND (= (LENGTH z) 6) (= z RR-NORMED-FIELD)))
    (have! '(NOT (= (LENGTH z) 7)) (lambda () (arith)))
    (mnp-nvs-length-claim! '(= z RR-NORMED-FIELD) 'z 7)
    (ai '(NOT (= (LENGTH z) 7)))))

;;; -----------------------------------------------------------------------
;;; 2d.  THE SECOND UNSATISFIABLE STRUCTURE PREDICATE (defective until
;;;      2026-08-23), and it survived the repair of the first one untouched.
;;;
;;; VECTOR-SPACE (finite-dimensional.scm) is `(same-shape-as MODULE)' plus one
;;; law.  MODULE declares `(substructure SCAL RING)', so the generated IFF
;;; carries (IS-RING (SCAL s)) and IS-RING pins length(scal(s)) = 6.  The law
;;; read `is-field(scal(s))', and IS-FIELD pins the SAME term to 8 -- FIELD is
;;; its own 8-slot shape, [CARR ADD MUL NEG ZERO ONE NON-ZERO RECIP]
;;; (field.scm).  Six against eight, so IS-VECTOR-SPACE(s) |- falsity, and
;;; IS-FINITE-DIMENSIONAL -- (AND (IS-VECTOR-SPACE m) (IS-NOETHERIAN m)) --
;;; inherited the emptiness.  hb-good-has-maximal, hahn-banach, norm-as-sup,
;;; norm-attained-by-functional and vector-taylor-remainder-bound were all
;;; vacuous on it, three of them ALSO vacuous through NORMED-VECTOR-SPACE (2c),
;;; whose repair fixed that cause and not this one.
;;;
;;; The repair states fieldhood OF A SIX-SLOT RING: IS-FIELD-RING (field.scm) is
;;; `(same-shape-as COMMUTATIVE-RING)' with ONE /= ZERO and every nonzero
;;; element invertible, so the law is `is-field-ring(scal(s))' and 6 = 6.
;;;
;;; ORDERING TRAP, the same one 2c documents: the NOT goes in FIRST, while the
;;; context holds only the 6 pin -- `arith' rewrites the goal with whatever
;;; length equation the context gives it, so landing the 8 first would let it
;;; rewrite with that one and decide nothing.  Hence the skip list.
;;; -----------------------------------------------------------------------

;;; The macete that unfolds IS-NAME, under either naming convention.
(define (mnp-unfold-name sym)
  (let ((r (vnb-guard (lambda () (resolve-macete-name sym)))))
    (if (or (vnb-error? r) (not r)) sym r)))

;;; Every structure-predicate assumption unfolded to atoms, SKIP excepted.
(define (mnp-vs-unfold! skip)
  (define (split!)
    (let loop ((n 0))
      (let ((h (let scan ((l (dk-asms)))
                 (cond ((null? l) #f)
                       ((and (pair? (car l)) (eq? (caar l) 'AND)) (car l))
                       (else (scan (cdr l)))))))
        (if (and h (< n 300)) (begin (ai h) (loop (+ n 1))) n))))
  (define (struct-pred f)
    (and (pair? f) (= (length f) 2) (symbol? (car f))
         (let ((str (symbol->string (car f))))
           (and (> (string-length str) 3) (string=? (substring str 0 3) "is-")
                (structure-declaration
                 (string->symbol (substring str 3 (string-length str))))))))
  (let loop ((n 0))
    (split!)
    (let ((h (let scan ((l (dk-asms)))
               (cond ((null? l) #f)
                     ((and (struct-pred (car l)) (not (member (car l) skip))) (car l))
                     (else (scan (cdr l)))))))
      (if (and h (< n 40))
          (begin (vnb-guard (lambda () (mac-h (mnp-unfold-name (car h)) h)))
                 (loop (+ n 1)))
          n))))

;;; Both spellings of the scalar-fieldhood conjunct: the defective one and the
;;; repaired one, so the SAME attack is red before the repair and green after.
(define mnp-vs-skip '((IS-FIELD (SCAL s)) (IS-FIELD-RING (SCAL s))))

(mnp-refuses "IS-VECTOR-SPACE(s) |- falsity -- the predicate must be SATISFIABLE"
  '(IMPLIES (IS-VECTOR-SPACE s) FALSITY)
  (lambda ()
    (di)
    (mnp-vs-unfold! mnp-vs-skip)
    ;; `vnb-guard', not `ignore-errors' (see 2c): `have!' raises a bare Scheme
    ;; error when its thunk leaves the side goal open, which is what happens
    ;; once the structure is repaired and nothing pins the term to 8.
    (vnb-guard
      (lambda ()
        (have! '(NOT (= (LENGTH (SCAL s)) 8)) (lambda () (arith)))
        (mnp-vs-unfold! '())
        (ai '(NOT (= (LENGTH (SCAL s)) 8)))))
    (mnp-attack-leaves!)))

;;; ANTI-VACUITY.  The refusal must be the DECLARATION's doing, not the attack
;;; going dead: the same derivation, move for move, against the defective
;;; pairing written out by hand.  It must CLOSE.
(mnp-control "the 6-against-8 derivation is LIVE (IS-RING and IS-FIELD of one term)"
  '(IMPLIES (AND (IS-RING (SCAL s)) (IS-FIELD (SCAL s))) FALSITY)
  (lambda ()
    (di)
    (ai '(AND (IS-RING (SCAL s)) (IS-FIELD (SCAL s))))
    (mnp-vs-unfold! '((IS-FIELD (SCAL s))))
    (have! '(NOT (= (LENGTH (SCAL s)) 8)) (lambda () (arith)))
    (mnp-vs-unfold! '())
    (ai '(NOT (= (LENGTH (SCAL s)) 8)))))

;;; -----------------------------------------------------------------------
;;; 2e.  THE CLASH TWO PREDICATES MAKE TOGETHER, which neither makes alone
;;;      (defective until 2026-08-23, and INVISIBLE to the gate written that
;;;      same morning).
;;;
;;; 2c and 2d are each ONE declaration contradicting itself, and
;;; `structure-satisfiability-audit' (audit.scm) decides that class.  It scans
;;; one DECLARATION at a time, so it cannot see this one:
;;;
;;;   IS-NORMED-VECTOR-SPACE(m)  pins length(m) = 7  (MODULE's six + VNRM);
;;;   IS-FINITE-DIMENSIONAL(m)   pins length(m) = 6  (IS-VECTOR-SPACE, hence
;;;                                                   MODULE's shape).
;;;
;;; Each is satisfiable alone.  Written of ONE m they are not, and hahn-banach,
;;; norm-as-sup, norm-attained-by-functional, vector-taylor-remainder-bound and
;;; nvs-taylor-remainder-bound all wrote them of one m -- so all five were
;;; VACUOUSLY true, on a ground unrelated to 2c and 2d and surviving both
;;; repairs.  The repaired statements say what the module half is ABOUT:
;;; IS-FINITE-DIMENSIONAL(NORMED-VECTOR-SPACE-AS-MODULE(m)), the six-slot
;;; projection (normed-vector-space.scm:136).
;;;
;;; The gate that DOES see it is `statement-satisfiability-audit' (audit.scm),
;;; which collects the pins of a whole HYPOTHESIS and follows a def-predicate
;;; into its defining IFF -- IS-FINITE-DIMENSIONAL is not a declared structure
;;; but (AND (IS-VECTOR-SPACE m) (IS-NOETHERIAN m)), so its pin is reachable no
;;; other way.
;;;
;;; ORDERING TRAP, as in 2c and 2d: the NOT goes in FIRST, while the context
;;; holds only the 6 pin.  `arith' rewrites the goal with whatever length
;;; equation the context gives it, so opening IS-NORMED-VECTOR-SPACE before the
;;; NOT lands would let it rewrite with the 7 and decide nothing.  Hence the
;;; skip list, and hence the def-predicate is opened by hand first.
;;; -----------------------------------------------------------------------

;;; IS-FINITE-DIMENSIONAL is a def-predicate, which mnp-vs-unfold! (2d) does not
;;; recognise -- it tests `structure-declaration'.  Open it by name, then let
;;; the structure walk take IS-VECTOR-SPACE down to its length conjunct.
(define (mnp-nfd-open! findim skip)
  (vnb-guard (lambda () (mac-h 'IS-FINITE-DIMENSIONAL findim)))
  (mnp-vs-unfold! skip))

(define mnp-nfd-view '(NORMED-VECTOR-SPACE-AS-MODULE m))

(mnp-refuses
  "IS-NORMED-VECTOR-SPACE(m) with IS-FINITE-DIMENSIONAL of the MODULE VIEW |- falsity"
  (list 'IMPLIES (list 'AND '(IS-NORMED-VECTOR-SPACE m)
                            (list 'IS-FINITE-DIMENSIONAL mnp-nfd-view))
        'FALSITY)
  (lambda ()
    (di)
    (ai (list 'AND '(IS-NORMED-VECTOR-SPACE m)
                   (list 'IS-FINITE-DIMENSIONAL mnp-nfd-view)))
    (mnp-nfd-open! (list 'IS-FINITE-DIMENSIONAL mnp-nfd-view)
                   '((IS-NORMED-VECTOR-SPACE m)))
    ;; `vnb-guard', not `ignore-errors' (see 2c): `have!' raises a bare Scheme
    ;; error when its thunk leaves the side goal open, which is exactly what
    ;; happens here -- the repaired pairing pins length(m) nowhere.
    (vnb-guard
      (lambda ()
        (have! '(NOT (= (LENGTH m) 7)) (lambda () (arith)))
        (mnp-vs-unfold! '())
        (ai '(NOT (= (LENGTH m) 7)))))
    (mnp-attack-leaves!)))

;;; ANTI-VACUITY, and it is the half that proves the attack is still live.  The
;;; refusal above must be the RESTATEMENT's doing, not the derivation going
;;; dead: here is the same derivation, move for move, against the defective
;;; pairing -- both predicates of one m -- written out by hand.  It must CLOSE.
(mnp-control
  "the 7-against-6 derivation is LIVE (both predicates of ONE m, by hand)"
  '(IMPLIES (AND (IS-NORMED-VECTOR-SPACE m) (IS-FINITE-DIMENSIONAL m)) FALSITY)
  (lambda ()
    (di)
    (ai '(AND (IS-NORMED-VECTOR-SPACE m) (IS-FINITE-DIMENSIONAL m)))
    (mnp-nfd-open! '(IS-FINITE-DIMENSIONAL m) '((IS-NORMED-VECTOR-SPACE m)))
    (have! '(NOT (= (LENGTH m) 7)) (lambda () (arith)))
    (mnp-vs-unfold! '())
    (ai '(NOT (= (LENGTH m) 7)))))

;;; -----------------------------------------------------------------------
;;; 2f.  THE SAME CLASH, THIRD FILE AND FOURTH APPEARANCE: three def-predicates
;;;      of the seminorm / Frechet vocabulary (defective until 2026-08-24).
;;;
;;; 2c and 2d are one DECLARATION contradicting itself and 2e is two predicates
;;; contradicting each other across one statement.  This is the third form: a
;;; `def-predicate' whose own BODY carries the pair, so the defining IFF makes
;;; the predicate EMPTY and every theorem assuming it vacuous.
;;;
;;;     (IS-MODULE m)              -> MODULE declares (substructure SCAL RING),
;;;                                   so the IFF carries (IS-RING (SCAL m)) and
;;;                                   IS-RING pins length(scal(m)) = 6
;;;     (IS-NORMED-FIELD (SCAL m)) -> NORMED-FIELD is its own SEVEN-slot shape
;;;                                   [CARR ADD MUL NEG ZERO ONE FNRM], pinning
;;;                                   the same term to 7
;;;
;;; IS-SEMINORM (seminorm-hahn-banach.scm) and IS-SEMINORM-FAMILY
;;; (frechet-open-mapping.scm) each wrote both; IS-FRECHET-STRUCTURE inherited
;;; the pair through IS-SEMINORM-FAMILY.  Six against seven, so all three were
;;; EMPTY and the four supports hahn-banach-seminorm, closed-graph-theorem,
;;; open-mapping-theorem and open-mapping-bounded-inverse were VACUOUSLY true.
;;;
;;; THE REPAIR IS NOT 2d's, and the difference is the point.  IS-VECTOR-SPACE
;;; was repaired by stating fieldhood OF A SIX-SLOT RING (IS-FIELD-RING), which
;;; keeps the pin visible to the audit.  That is unavailable here: IS-SEMINORM's
;;; absolute-homogeneity law reads FNRM -- the one slot
;;; NORMED-FIELD-AS-COMMUTATIVE-RING DROPS -- so no six-slot predicate can state
;;; it.  The field is therefore NAMED, and the module's scalars pinned to its
;;; ring view:
;;;
;;;     FORSOME fld.  IS-NORMED-FIELD(fld)
;;;                   and scal(m) = normed-field-as-commutative-ring(fld)
;;;                   and ... p(act(m)(lam, x)) = (fnrm(fld))(lam) * p(x)
;;;
;;; hahn-banach-seminorm names it with a UNIVERSAL binder instead, its
;;; conclusion reading the same norm.
;;;
;;; WHY THIS SECTION EXISTS AT ALL: `statement-satisfiability-audit' flattens
;;; conjunctions and does NOT descend into a FORSOME, so after the repair it
;;; cannot see the scalar pin either way.  The audit reported all seven names
;;; (the three definitions and the four supports, ten findings counting one per
;;; clashing term) before the repair and reports none after -- but a gate that
;;; has stopped looking and a gate that finds nothing read alike, so the refusal
;;; is checked here directly.
;;;
;;; ORDERING TRAP, the same one 2c/2d/2e document: the NOT goes in FIRST, while
;;; the context holds only the 6 pin.  `arith' rewrites the goal with whatever
;;; length equation the context gives it, so unfolding IS-NORMED-FIELD before
;;; the NOT lands would let it rewrite with the 7 and decide nothing.  Hence the
;;; skip list -- inert after the repair, since no such atom is produced.
;;;
;;; MUTATION-CHECKED 2026-08-24, and not by construction: the two definitions
;;; were put back to the defective pair in place and the corpus re-run.  All
;;; THREE refusals below went red (expected #f got #t) and the control stayed
;;; green; restored, 38/0.  So the entries discriminate the repair from the
;;; defect, and the control discriminates a repair from an attack that has died.
;;; The standalone derivation, which also measures the pins in each direction,
;;; is scratchpad/sn-falsity-probe.scm.
;;; -----------------------------------------------------------------------

;;; The atom the ordering trap requires be unfolded LAST.  Nothing produces it
;;; after the repair, so the skip is inert there and load-bearing before it.
(define mnp-sn-skip '((IS-NORMED-FIELD (SCAL m))))

;;; Open the named def-predicate hypotheses in order, taking the structure
;;; predicates down to atoms between them.  `mnp-vs-unfold!' (2d) tests
;;; `structure-declaration', so it does not recognise a def-predicate at all --
;;; each has to be opened by name, and IS-FRECHET-STRUCTURE needs two rounds
;;; because its scalar clause is IS-SEMINORM-FAMILY's.
(define (mnp-sn-open! atoms skip)
  (for-each (lambda (a)
              (mnp-vs-unfold! skip)
              (vnb-guard (lambda () (mac-h (mnp-unfold-name (car a)) a))))
            atoms)
  (mnp-vs-unfold! skip))

;;; The attack, once: open, land the NOT while only the 6 is in view, unfold the
;;; rest, and NOT-eliminate.  `vnb-guard', not `ignore-errors' (see 2c): `have!'
;;; raises a bare Scheme error when its thunk leaves the side goal open, which is
;;; exactly what happens once nothing pins the term to 7.
(define (mnp-sn-attack! atoms)
  (di)
  (mnp-sn-open! atoms mnp-sn-skip)
  (vnb-guard
    (lambda ()
      (have! '(NOT (= (LENGTH (SCAL m)) 7)) (lambda () (arith)))
      (mnp-vs-unfold! '())
      (ai '(NOT (= (LENGTH (SCAL m)) 7)))))
  (mnp-attack-leaves!))

(mnp-refuses "IS-SEMINORM(m, p) |- falsity -- the predicate must be SATISFIABLE"
  '(IMPLIES (IS-SEMINORM m p) FALSITY)
  (lambda () (mnp-sn-attack! '((IS-SEMINORM m p)))))

(mnp-refuses "IS-SEMINORM-FAMILY(m, fam) |- falsity -- the predicate must be SATISFIABLE"
  '(IMPLIES (IS-SEMINORM-FAMILY m fam) FALSITY)
  (lambda () (mnp-sn-attack! '((IS-SEMINORM-FAMILY m fam)))))

(mnp-refuses "IS-FRECHET-STRUCTURE(m, fam) |- falsity -- the predicate must be SATISFIABLE"
  '(IMPLIES (IS-FRECHET-STRUCTURE m fam) FALSITY)
  (lambda ()
    (mnp-sn-attack! '((IS-FRECHET-STRUCTURE m fam) (IS-SEMINORM-FAMILY m fam)))))

;;; ANTI-VACUITY, and it is what makes the three refusals above mean anything.
;;; The SAME derivation, move for move, against the conjunction those three
;;; definitions used to carry, written out by hand.  It must CLOSE.  If it stops
;;; closing, the attack has gone dead and the refusals assert nothing.
(mnp-control
  "the 6-against-7 derivation is LIVE (IS-MODULE and IS-NORMED-FIELD of one m, by hand)"
  '(IMPLIES (AND (IS-MODULE m) (IS-NORMED-FIELD (SCAL m))) FALSITY)
  (lambda ()
    (di)
    (ai '(AND (IS-MODULE m) (IS-NORMED-FIELD (SCAL m))))
    (mnp-vs-unfold! mnp-sn-skip)
    (have! '(NOT (= (LENGTH (SCAL m)) 7)) (lambda () (arith)))
    (mnp-vs-unfold! '())
    (ai '(NOT (= (LENGTH (SCAL m)) 7)))))

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

;;; The STRICT/NON-STRICT boundary of the refutation test, which the entry above
;;; does not reach.  Found 2026-08-06 by a SUBTLE mutation (worklist item 4 of
;;; docs/notes-mutation-testing-2026-08-06.md): `con-contradictory?'
;;; (linear-arith.scm:80) calls a constant constraint k <= 0 contradictory when
;;; k > 0, and changing that one test to k >= 0 is unsound -- yet it turned
;;; NOTHING in this corpus red.  The reason is that `a <= b |- b < a' produces
;;; two constraints that are both positive on `a', so elimination drops them
;;; one-sided and no constant constraint is ever formed: the boundary was
;;; untested, not merely untested-by-that-mutant.
;;;
;;; This goal does form one.  From a <= b and b <= a, eliminating `a' combines
;;; them into 0 <= 0, which is satisfiable (a = b) and which the off-by-one
;;; reads as a contradiction -- and a contradiction closes anything, here the
;;; false a < b.  Verified both ways: open at baseline, CLOSED under the mutant.
(mnp-refuses "a <= b, b <= a  |-  a < b   [false: 0 <= 0 is not a contradiction]"
  '(FORALL a_ (IMPLIES (IN a_ RR) (FORALL b_ (IMPLIES (IN b_ RR)
     (IMPLIES (<= a_ b_) (IMPLIES (<= b_ a_) (< a_ b_)))))))
  (lambda () (di) (di) (di)
    (ignore-errors (ineq (mnp-idx '(<= a_ b_)) (mnp-idx '(<= b_ a_))))
    (mnp-attack!)))

;;; ... with the same two premises and the same two indices closing a TRUE goal,
;;; so the refusal above is about the strict conclusion and not about `ineq'
;;; being inert on this context.
(mnp-control "a <= b, b <= a  |-  a <= b   [same premises, same indices]"
  '(FORALL a_ (IMPLIES (IN a_ RR) (FORALL b_ (IMPLIES (IN b_ RR)
     (IMPLIES (<= a_ b_) (IMPLIES (<= b_ a_) (<= a_ b_)))))))
  (lambda () (di) (di) (di)
    (ineq (mnp-idx '(<= a_ b_)) (mnp-idx '(<= b_ a_)))))

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
