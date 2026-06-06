;;; scratch-roadtest.scm -- a verified ladder of small proofs for road-testing
;;; new features (especially the forthcoming warrant / proof-debt ledger).
;;;
;;; Load AFTER the prover:  (load "load.scm")  then  (load "scratch-roadtest.scm")
;;; Running it proves and qed-installs each fixture under an rt-* / demo-* name,
;;; printing PROVED / OPEN per item and a summary.  Re-running just redefines
;;; the demo theorems (harmless).  Or copy any single block into the REPL.
;;;
;;; Each fixture is annotated with what it CITES and the bill the debt ledger
;;; should report -- so the same ladder exercises the ledger once it exists:
;;;   * empty debt (no citation), single citations across warrant states
;;;     (informal / well-known / asserted-no-warrant), a 2-element bill, and
;;;     the transitive case (B cites proven A -> debt resolves THROUGH A).
;;;
;;; Tactic notes (verified 2026-06-03):
;;;   - di peels one forall OR one implies; on forall x.(P=>Q) it does both.
;;;     Just di until the goal is atomic; an extra di on an atomic goal prints
;;;     a harmless "cannot decompose" warning and changes nothing.
;;;   - (bc* 'name () s1 s2 ...): one subproof per lemma HYPOTHESIS; (ass)
;;;     discharges a hypothesis already in the assumptions.
;;;   - bc* matches the lemma CONCLUSION; it cannot match a conclusion whose
;;;     head is a structure-accessor application like ((MUL s) x y), so the
;;;     equational structure axioms (monoid-left-id, ring-left-dist, ...) are
;;;     NOT citable this way (and are inert as macetes) -- omitted here.
;;;   - AND goals: (di) splits; focus auto-advances to the next open conjunct.

;;; --- harness ---------------------------------------------------------

(define *rt-pass* 0)
(define *rt-fail* 0)

;;; Run one fixture THUNK (which starts a proof and applies tactics); if it
;;; closes, qed-install under NAME.  Report PROVED / OPEN; tally.
(define (rt name cites thunk)
  (display "=== ") (display name)
  (display "   [cites: ") (display cites) (display "]") (newline)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler
      (lambda (e)
        (display "  ERROR: ") (display (condition/report-string e)) (newline)
        (set! *rt-fail* (+ *rt-fail* 1)) (k #f))
      (lambda ()
        ;; Run the tactic thunk quietly -- suppress each step's goal-tree
        ;; dump so only the per-fixture header, the qed ledger line, and
        ;; PROVED/OPEN show.  qed runs OUTSIDE the quiet extent (its `modulo'
        ;; line uses display, not show), so the warrant bill stays visible.
        (fluid-let ((*vnb-quiet* #t)) (thunk))
        (cond
          ((and *ps* (proof-done? *ps*))
           (qed name)
           (set! *rt-pass* (+ *rt-pass* 1))
           (display "  PROVED -> qed ") (display name) (newline))
          (else
           (set! *rt-fail* (+ *rt-fail* 1))
           (display "  OPEN\n"))))))))

;;; ====================================================================
;;; A. Sanity -- no citation.  Expected debt: {}  (modulo 0, unconditional)
;;; ====================================================================

(rt 'rt-trivial '()
  (lambda ()
    (sp (make-wff '(FORALL x (IMPLIES (IN x SET) (IN x SET)))))
    (di)(di)(ass)))

;;; ====================================================================
;;; B. Single citation.  Expected debt: { the one cited fact }
;;; ====================================================================

;; cites finsum-empty  (asserted, no warrant recorded)
(rt 'rt-finsum-empty 'finsum-empty
  (lambda ()
    (sp (make-wff '(FORALL ag (FORALL f (= (FINSUM ag f EMPTY-SET) (E ag))))))
    (di)(di)(bc* 'finsum-empty ())))

;; cites card-empty  (macete path)
(rt 'rt-card-empty 'card-empty
  (lambda ()
    (sp (make-wff '(= (CARD EMPTY-SET) 0)))
    (mac 'card-empty)(rfl)))

;; cites card-power-nn  (warrant: well-known)
(rt 'rt-card-power 'card-power-nn
  (lambda ()
    (sp (make-wff '(FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
                      (IN (CARD (POWER X)) NN)))))
    (di)(di)(bc* 'card-power-nn () (ass))))

;; cites prod-ring-empty  (warrant: informal)
(rt 'rt-prod-empty 'prod-ring-empty
  (lambda ()
    (sp (make-wff '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
                    (FORALL f (= (PROD-RING R f EMPTY-SET) (ONE R)))))))
    (di)(di)(di)(bc* 'prod-ring-empty () (ass))))

;; cites prod-ring-singleton  (warrant: informal)
(rt 'rt-prod-singleton 'prod-ring-singleton
  (lambda ()
    (sp (make-wff '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
                    (FORALL x (IMPLIES (IN x SET)
                    (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (A R)))
                      (= (PROD-RING R f (PAIR x x)) (f x))))))))))
    (di)(di)(di)(di)(di)(bc* 'prod-ring-singleton () (ass)(ass)(ass))))

;; cites finsum-singleton
(rt 'rt-finsum-singleton 'finsum-singleton
  (lambda ()
    (sp (make-wff '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
                    (FORALL x (IMPLIES (IN x SET)
                    (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (A ag)))
                      (= (FINSUM ag f (PAIR x x)) (f x))))))))))
    (di)(di)(di)(di)(di)(bc* 'finsum-singleton () (ass)(ass)(ass))))

;;; ====================================================================
;;; C. Multi-citation.  Expected debt: { card-empty, finsum-empty }
;;; ====================================================================

(rt 'rt-and-two '(card-empty finsum-empty)
  (lambda ()
    (sp (make-wff '(AND (= (CARD EMPTY-SET) 0)
                        (FORALL ag (FORALL f (= (FINSUM ag f EMPTY-SET) (E ag)))))))
    (di)
    (mac 'card-empty)(rfl)
    (di)(di)(bc* 'finsum-empty ())))

;;; ====================================================================
;;; D. Transitivity -- the key ledger test.  Run A then B.
;;;    debt(demo-empty-prod-2) should resolve THROUGH the proven
;;;    demo-empty-prod to { prod-ring-empty } -- NOT { demo-empty-prod }.
;;; ====================================================================

;; A: cites prod-ring-empty directly
(rt 'demo-empty-prod 'prod-ring-empty
  (lambda ()
    (sp (make-wff '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
                    (FORALL f (= (PROD-RING R f EMPTY-SET) (ONE R)))))))
    (di)(di)(di)(bc* 'prod-ring-empty () (ass))))

;; B: cites only the proven demo-empty-prod
(rt 'demo-empty-prod-2 'demo-empty-prod
  (lambda ()
    (sp (make-wff '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
                    (FORALL f (= (PROD-RING R f EMPTY-SET) (ONE R)))))))
    (di)(di)(di)(bc* 'demo-empty-prod () (ass))))

;;; --- summary ---------------------------------------------------------

(newline)
(display ";; roadtest: ") (display *rt-pass*) (display " proved, ")
(display *rt-fail*) (display " open/error of ")
(display (+ *rt-pass* *rt-fail*)) (display " fixtures.") (newline)
