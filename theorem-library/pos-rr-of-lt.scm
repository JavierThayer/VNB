;;; pos-rr-of-lt.scm -- 0 < x IMPLIES POS-RR(x), the bridge the tree did not
;;; have, and `nn-recip-succ-pos' retired as a four-line consequence of it.
;;;
;;;     rr-pos-rr-of-lt:   x in RR,  0 < x   =>   POS-RR(x)
;;;     nn-recip-succ-pos: n in NN           =>   POS-RR(recip(n + 1))
;;;
;;; WHY THE BRIDGE IS THE POINT.  `POS-RR' (structure-library/order-predicates.scm)
;;; is the "eps > 0" predicate every eps-argument in the tree instantiates, and
;;; before this file **`nn-recip-succ-pos' was the only theorem in the whole
;;; library whose conclusion was a POS-RR at all** -- measured over
;;; *theorem-table*.  Every other route into the predicate was an unfold: a
;;; driver that had `0 < t' in hand and wanted `POS-RR(t)' had to `mac' the
;;; definition, split a right-nested three-fold conjunction, and discharge the
;;; three pieces by hand.  So the one general fact was missing and the one instance
;;; of it was asserted.  Proving the general fact makes the instance free, and
;;; the next such instance free as well.
;;;
;;; WHAT IT COSTS: nothing, both `modulo 0'.
;;;
;;; THE RETIRED SUPPORT, and its warrant is the reason to read this note.
;;; `nn-recip-succ-pos' stood in order-predicates.scm as an `informal' support
;;; whose warrant said, in terms: "Not mechanised: it needs recip-order lemmas
;;; the tree does not have yet."  The tree has had them since
;;; theorem-library/rr-recip-order.scm -- `rr-recip-pos' is exactly the lemma
;;; named -- and nothing went back to collect.  That is the same species as the
;;; comment CLAUDE.md warns about (the derivation written out in prose and then
;;; not run) and as integral-domain-laws.scm sitting on disk unloaded: a proof
;;; that exists everywhere except in the checker.  The statement re-installed
;;; here is BYTE-IDENTICAL to the retired one -- the install reports
;;; "re-installing the same statement", not the "DIFFERENT statement" warning --
;;; so every citer (compact-separable-proof, sequential-continuity) sees the
;;; formula it always saw.
;;;
;;; TWO MECHANICS, both of them CLAUDE.md entries met in the flesh:
;;;
;;;  * `rr-add-closed' and `rr-recip-closed' have CONJUNCTIVE antecedents, and
;;;    `fact' will not split one.  Without a `have!' of the AND immediately
;;;    before, the citation lands the IMPLICATION, silently, and `n_ + 1' is
;;;    never typed -- after which `rr-recip-pos' will not detach either and the
;;;    failure surfaces three steps later as an `ass' that cannot match.
;;;  * the unfolded POS-RR is a RIGHT-NESTED conjunction, so one `di' leaves an
;;;    AND standing.  Split to the leaves and dispatch on each.
;;;
;;; Loads after rr-recip-order (rr-recip-pos), rr-order-basics (rr-pos-ne-zero),
;;; nn-order-ord (nn-zero-le) and equality-basics (neq-sym); must PRECEDE
;;; compact-separable-proof, the earliest citer of nn-recip-succ-pos.

(define (prl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "prl-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (prl-ineq . fs) (apply ineq (map prl-idx fs)))

;;; The conjunctive-goal splitter this file carried (prl-split-and!) is
;;; `dk-conj-close!' in driver-kit.scm since 2026-09-14.

;;; =======================================================================
;;; The bridge.
;;; =======================================================================

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (IMPLIES (< 0 x) (POS-RR x))))))
(di) (di)
(fact 'rr-pos-ne-zero 'x)             ; not(x = 0)
(fact 'neq-sym 'x 0)                  ; ... in the orientation POS-RR wants
(mac 'pos-rr)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IN)  (ass))
           ((eq? (car g) 'NOT) (ass))
           (else (prl-ineq '(< 0 x)))))))
(qed 'rr-pos-rr-of-lt)
(topic! 'rr-pos-rr-of-lt 'inequalities)
(alias! 'rr-pos-rr-of-lt "a positive real satisfies POS-RR")

;;; =======================================================================
;;; ... and the reciprocal instance, which is now four lines of arithmetic.
;;; Statement byte-identical to the support this file retires.
;;; =======================================================================

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (POS-RR (recip (+ n_ 1)))))))
(di)
(fact 'nn-in-rr 'n_)
(fact 'nn-zero-le 'n_)
(fact 'rr-one-in)
;; rr-add-closed has a CONJUNCTIVE antecedent: land the AND, or the citation
;; lands the implication and n_ + 1 is never typed.
(have! '(AND (IN n_ RR) (IN 1 RR)))
(fact 'rr-add-closed 'n_ 1)
(have! '(< 0 (+ n_ 1)) (lambda () (prl-ineq '(<= 0 n_))))
(fact 'rr-recip-pos '(+ n_ 1))
(have! '(AND (IN (+ n_ 1) RR) (NOT (= (+ n_ 1) 0)))
  (lambda () (fact 'rr-pos-ne-zero '(+ n_ 1)) (prop)))
(fact 'rr-recip-closed '(+ n_ 1))
(fact 'rr-pos-rr-of-lt '(recip (+ n_ 1)))
(ass)
(qed 'nn-recip-succ-pos)
(topic! 'nn-recip-succ-pos 'inequalities)
