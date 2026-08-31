;;; rr-le-all-pos.scm -- a real below every positive real is non-positive,
;;; PROVEN.
;;;
;;;     rr-le-all-pos-nonpos:  x in RR  =>  (forall eps. POS-RR(eps) => x <= eps)
;;;                                     =>  x <= 0
;;;
;;; It was a `well-known' support in structure-library/order-predicates.scm, and
;;; that file's own header named it as one of five facts that "are now
;;; DERIVABLE, and each is a theorem waiting for a driver rather than a
;;; permanent assertion".  This is the driver.  It was the largest single leaf
;;; left in the library by the measurement that matters: 20 bills of which it is
;;; the SOLE asserted leaf -- the head of the greedy what-if ranking, ahead of
;;; nn-mul-succ (8) and metric-dist-real (8).
;;;
;;; WHAT UNBLOCKED IT.  `rr-pos-halvable' (theorem-library/rr-halving.scm,
;;; PROVEN 2026-08-17, loads immediately above).  The mathematics is the one
;;; line every textbook gives: if x were positive it would be <= its own half,
;;; and a positive real is strictly above its half.  Completeness is NOT
;;; involved -- the header of order-predicates.scm reads this fact as "the
;;; order-density / archimedean face of completeness", but the halving witness
;;; eps * recip(1+1) is an ordered-FIELD construction, so the proof below is
;;; field + order only.  It cites no archimedean fact and none of the SUP
;;; axioms.
;;;
;;; THE SHAPE.  `pbc', then a case split on x = 0:
;;;
;;;   x = 0    -- reflexivity at 0, rewritten back along the equation.
;;;   x /= 0   -- totality gives 0 <= x (the other disjunct is the negation
;;;               `pbc' put in the context, so `prop' selects it), hence
;;;               POS-RR(x); halving gives d > 0 with d + d = x; the hypothesis
;;;               at d gives x <= d; and 2(x - d) + (d + d - x) = x, so
;;;               x <= 0 -- one `ineq' whose Farkas certificate does not even
;;;               need d's positivity.
;;;
;;; TWO ORDERING CONSTRAINTS IN THE DRIVER, both of them the destructive-`mac-h'
;;; trap (CLAUDE.md).  The instantiation of the hypothesis at d must come BEFORE
;;; POS-RR(d) is unfolded, because `mac-h' REPLACES the assumption that `inst+'
;;; forward-detaches against; and `ineq' premise indices are 1-BASED
;;; (ineq-oracle.scm:206), so a 0-based finder silently names the neighbouring
;;; formulas and the oracle then blames the goal.
;;;
;;; Loads after rr-halving (rr-pos-halvable), equality-basics (neq-sym) and
;;; `prop'; and BEFORE its citers, the earliest of which is
;;; theorem-library/dominated-convergence.

;;; ---- file-local driver helpers (the `rlp-' prefix) -------------------

;; 1-BASED index of a context formula, for `ineq' (see the header).  Errors on
;; a miss: a finder that returns #f would leave the premise list quietly short.
(define (rlp-idx f)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "rlp-idx: not in context" f))
          ((equal? (car as) f) i)
          (else (loop (cdr as) (+ i 1))))))

(sp (make-wff '(FORALL x (IMPLIES (IN x RR)
     (IMPLIES (FORALL eps (IMPLIES (POS-RR eps) (<= x eps)))
              (<= x 0))))))
(di)                                    ; x in RR
(di)                                    ; the eps-hypothesis; goal x <= 0
(pbc)                                   ; not(x <= 0) in context, goal falsity

(define rlp-cases (dk-opened (lambda () (use-em '(= x 0)))))

;;; ---- x = 0: reflexivity, rewritten along the equation ----------------
(dk-focus! (car rlp-cases))
(fact 'rr-zero-in)
(have! '(<= x 0)
       (lambda () (subst '(= x 0)) (fact 'rr-leq-reflexive 0) (ass)))
(ai '(NOT (<= x 0)))

;;; ---- x /= 0: x is positive, so it is <= its own half -----------------
(dk-focus! (cadr rlp-cases))
(fact 'rr-zero-in)
(have! '(AND (IN x RR) (IN 0 RR)))
(fact 'rr-leq-total 'x 0)               ; x <= 0 or 0 <= x
(have! '(<= 0 x) (lambda () (prop)))    ; the left disjunct is negated in context
(fact 'neq-sym 'x 0)                    ; POS-RR wants not(0 = x)
(have! '(POS-RR x) (lambda () (mac 'pos-rr) (from-context!)))
(dk-fact! 'rr-pos-halvable 'x)

;; skolemize the half locally: `obtain' cannot see an existential that is
;; already in the context (CLAUDE.md), so read the eigenvariable off the
;; landing rather than guessing its name.
(define rlp-ex (dk-landed-1 (lambda ()
  (ai '(FORSOME d (AND (POS-RR d) (= (+ d d) x)))))))
(define rlp-d (cadr (cadr rlp-ex)))
(dk-split! rlp-ex)

;; instantiate BEFORE unfolding: `mac-h' would delete the POS-RR(d) that
;; `inst+' detaches against.
(inst+ '(FORALL eps (IMPLIES (POS-RR eps) (<= x eps))) rlp-d)
(mac-h 'pos-rr (list 'POS-RR rlp-d))
(dk-split! (list 'AND (list 'IN rlp-d 'RR)
                 (list 'AND (list '<= 0 rlp-d) (list 'NOT (list '= 0 rlp-d)))))

(have! '(<= x 0)
       (lambda ()
         (ineq (rlp-idx (list '<= 0 rlp-d))
               (rlp-idx (list 'IN rlp-d 'RR))
               (rlp-idx (list '<= 'x rlp-d))
               (rlp-idx (list '= (list '+ rlp-d rlp-d) 'x))
               (rlp-idx '(IN x RR)))))
(ai '(NOT (<= x 0)))

(qed 'rr-le-all-pos-nonpos)
(topic! 'rr-le-all-pos-nonpos 'analysis)
