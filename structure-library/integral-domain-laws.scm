;;; integral-domain-laws.scm -- integral-domain-cancel-zero, PROVEN from the
;;; definition.
;;;
;;; integral-domain-cancel-zero (a*b = 0 and b /= 0  =>  a = 0) was asserted in
;;; integral-domain.scm with a raw `theory-add-axiom!' and -- alone among the
;;; facts on Cor 3.46's critical path -- carried NO `warrant!' at all, so it had
;;; no trust tier and slipped silently into every bill that cited it.  It also
;;; was not independent: `is-integral-domain-def' is an IFF whose body already
;;; states
;;;
;;;     forall a,b in CARR(s).  a*b = 0  =>  (a = 0 OR b = 0)
;;;
;;; so cancel-zero is that conjunct instantiated and OR-eliminated against the
;;; hypothesis b /= 0.  A redundant asserted axiom -- a registration oversight of
;;; exactly the kind metric-laws.scm and bijection-derived.scm were written to
;;; retire.  This file retires it: PROVEN modulo 0 by unfolding the definition.
;;;
;;; NOTE the `warrant-invariant' gate does NOT catch this class.  It checks that
;;; no asserted fact CLAIMS a proof; it does not check that every asserted fact
;;; HAS a warrant.  Raw theory-add-axiom! facts are invisible to the trust tiers.
;;;
;;; Loaded after interactive + proof-debt (needs sp/di/mac-h/ai/inst+/qed).

;; ---- proof-driver helpers (idl- prefix; never named like a tactic) ----
(define (idl-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (idl-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (idl-wf v b) (fold-right (lambda (x y) `(FORALL ,x ,y)) b v))
(define (idl-wi p b) (fold-right (lambda (x y) `(IMPLIES ,x ,y)) b p))
(define (idl-di*) (let lp () (let* ((g (idl-goal)) (h (and (pair? g) (car g))))
                    (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (idl-find pred)
  (let ((r (filter pred (idl-asms))))
    (if (null? r) (error "integral-domain-laws: no assumption matching") (car r))))
(define (idl-head? h) (lambda (f) (and (pair? f) (eq? (car f) h))))
(define (idl-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd))
                            (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (idl-goalof l) (wff-formula (sequent-node-assertion l)))
(define (idl-focus! pred)                       ; ERRORS on a miss
  (let lp ((ls (idl-leaves)))
    (cond ((null? ls) (error "integral-domain-laws: no leaf matches"))
          ((pred (idl-goalof (car ls))) (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (lp (cdr ls))))))
;; split every AND assumption until none remain
(define (idl-split-ands!)
  (let lp ((n 0))
    (when (< n 8)
      (let ((a (filter (idl-head? 'AND) (idl-asms))))
        (when (pair? a) (ai (car a)) (lp (+ n 1)))))))

(sp (make-wff
  (idl-wf '(s) (idl-wi '((IS-INTEGRAL-DOMAIN s))
    (idl-wf '(a) (idl-wi '((IN a (CARR s)))
      (idl-wf '(b) (idl-wi '((IN b (CARR s))
                             (= ((MUL s) a b) (ZERO s))
                             (NOT (= b (ZERO s))))
        '(= a (ZERO s))))))))))
(idl-di*)

;; unfold the definition and project the no-zero-divisor conjunct
(mac-h 'is-integral-domain-def '(IS-INTEGRAL-DOMAIN s))
(idl-split-ands!)

;; forall a in CARR. forall b in CARR. a*b = 0 => (a = 0 OR b = 0)
(define IDL-NZD
  (idl-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (let ((body (caddr f)))
                               (and (pair? body) (eq? (car body) 'IMPLIES)
                                    (equal? (cadr body) (list 'IN (cadr f) '(CARR s)))))))))
(inst+ IDL-NZD 'a)
(define IDL-INNER
  (idl-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (let ((body (caddr f)))
                               (and (pair? body) (eq? (car body) 'IMPLIES)
                                    (equal? (cadr body) (list 'IN (cadr f) '(CARR s)))))
                             (not (equal? f IDL-NZD))))))
(inst+ IDL-INNER 'b)

;; the disjunction (a = 0 OR b = 0) is now in context; case-split it
(ai (idl-find (idl-head? 'OR)))

;; branch 1: a = 0 -- the goal
(idl-focus! (lambda (g) (equal? g '(= a (ZERO s)))))
(ass)

;; branch 2: b = 0 contradicts the hypothesis b /= 0
(idl-focus! (lambda (g) (equal? g '(= a (ZERO s)))))
(ai '(NOT (= b (ZERO s))))

(if (proof-done? *ps*)
    (begin (qed 'integral-domain-cancel-zero)
           (topic! 'integral-domain-cancel-zero 'algebra))
    (begin (display "@@@ INCOMPLETE -- open leaves:") (newline)
           (for-each (lambda (l) (display "@@@   ") (write (idl-goalof l)) (newline))
                     (idl-leaves))
           (error "integral-domain-laws: proof did not complete")))

;;; =======================================================================
;;; integral-domain-nontrivial : ONE(s) /= ZERO(s).
;;;
;;; The sibling oversight, and a shorter one: this is not an instance of a
;;; conjunct of is-integral-domain-def, it IS one, verbatim.  It was asserted in
;;; integral-domain.scm with the comment "a conjunct of is-integral-domain-def,
;;; surfaced as a citable theorem" -- which is the proof, written out in prose
;;; and then not run.  Unfold the hypothesis, split, and it is in the context.
(sp (make-wff '(FORALL s (IMPLIES (IS-INTEGRAL-DOMAIN s)
                 (NOT (= (ONE s) (ZERO s)))))))
(idl-di*)                                ; peels FORALL/IMPLIES, stops at the NOT
(mac-h 'is-integral-domain-def '(IS-INTEGRAL-DOMAIN s))
(idl-split-ands!)
(ass)

(if (proof-done? *ps*)
    (begin (qed 'integral-domain-nontrivial)
           (topic! 'integral-domain-nontrivial 'algebra))
    (begin (display "@@@ INCOMPLETE (nontrivial) -- open leaves:") (newline)
           (for-each (lambda (l) (display "@@@   ") (write (idl-goalof l)) (newline))
                     (idl-leaves))
           (error "integral-domain-laws: integral-domain-nontrivial did not complete")))
