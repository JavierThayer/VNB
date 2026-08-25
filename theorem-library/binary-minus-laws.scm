;;; binary-minus-laws.scm -- what follows from `binary-minus-def'.
;;;
;;; number-systems.scm gained the defining equation for BINARY minus on
;;; 2026-08-01:
;;;
;;;     forall a, b.   (- a b)  ==  a + (- b)
;;;
;;; Before it, every minus axiom in the base was UNARY (rr-neg-closed,
;;; rr-neg-inverse and their ZZ/QQ/CC counterparts), while the parser emits the
;;; binary form for "x - y" (parser.scm:9).  Nothing connected the two, so
;;; nothing in the theory said that `u - v' was a difference, or that RR was
;;; closed under it.
;;;
;;; This file cashes that.  `rr-sub-in-rr' -- RR closed under subtraction -- used
;;; to be a `well-known' PSS support in structure-library/order-lemmas.scm; it
;;; read like a triviality restating rr-add-closed, and was in fact the ONLY
;;; constraint anywhere on an uninterpreted binary head.  It is now a theorem.
;;;
;;; WHY THIS ONE MATTERED more than its statement suggests: `ineq', the
;;; Fourier-Motzkin/Farkas closer, is a TRUSTED oracle that "linearizes over
;;; + - *" by its own documentation.  It therefore reads (- a b) as subtraction
;;; when it discharges a goal.  Until binary-minus-def existed, that reading was
;;; the oracle's own assumption rather than something the theory licensed --
;;; and every Farkas certificate over a difference depended on it.
;;;
;;; Loads after interactive/proof-debt (sp/di/mac/fact/have!/detach!/qed) and
;;; before theorem-library/differentiation, the one consumer of rr-sub-in-rr.

;; ---- file-local helper (bm- prefix; never named like a tactic) ------------
;; Focus the leaf whose goal is EXACTLY form.  Exists because `ass' hands focus
;; to an engine-chosen leaf, and because substring matching on goals is
;; ambiguous once a proof has several leaves of the same shape.  It ERRORS on a
;; miss rather than returning #f: a focus helper that silently leaves focus put
;; hides every later mistake.
(define (bm-focus-exact form)
  (let loop ((l (proof-leaves)))
    (cond ((null? l) (error "bm-focus-exact: no leaf with goal" form))
          ((equal? (wff-formula (sequent-node-assertion (car l))) form)
           (dk-focus! (car l)))
          (else (loop (cdr l))))))

;;; rr-sub-in-rr: RR is closed under binary subtraction.
;;;
;;; Three di's, not one: di takes the leading FORALL prefix, and each guard then
;;; needs its own call.  The `mac' is the whole content -- binary-minus-def is
;;; declare-named-only!, so it must be cited by name and will not fire from the
;;; rewrite index.  The closing dance (have! the conjunction, then detach!)
;;; exists because rr-add-closed states its hypotheses as an AND, and neither
;;; `fact' nor `inst+' will split a conjunctive antecedent; rr-neg-closed, being
;;; single-antecedent, detaches by itself.
(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR))
                              '(IN (- u v) RR))))
(di) (di) (di)
(mac 'binary-minus-def)
(fact 'rr-neg-closed 'v)
(fact 'rr-add-closed 'u '(- v))
(have! '(AND (IN u RR) (IN (- v) RR))
       (lambda () (di) (ass) (bm-focus-exact '(IN (- v) RR)) (ass)))
(detach! '(IMPLIES (AND (IN u RR) (IN (- v) RR)) (IN (+ u (- v)) RR)))
(ass)
(qed 'rr-sub-in-rr)
(topic! 'rr-sub-in-rr 'plumbing)

;;; zz-sub-in-zz: ZZ is closed under binary subtraction.
;;;
;;; The exact sibling of rr-sub-in-rr above, and it was missing for the same
;;; reason: every ZZ minus axiom in number-systems.scm is UNARY (zz-neg-closed,
;;; zz-neg-inverse), while the parser emits the binary `(- u v)'.  Nothing said
;;; a difference of integers is an integer.  Added 2026-08-24 for the Bernstein
;;; moments, whose COMB-KK index runs over ZZ precisely so that k-1 is total at
;;; k = 0 -- so `(- k 1) in ZZ' is what every pointwise typing of the basis
;;; family at a shifted index needs.
;;;
;;; Same shape as rr-sub-in-rr: binary-minus-def is `declare-named-only!' and
;;; must be cited by name; zz-add-closed states its hypotheses as an AND, which
;;; neither `fact' nor `inst+' will split, hence the have!/detach! pair.
(sp (make-wff (forall-guarded '(u_ v_) (list '(IN u_ ZZ) '(IN v_ ZZ))
                              '(IN (- u_ v_) ZZ))))
(di) (di) (di)
(mac 'binary-minus-def)
(fact 'zz-neg-closed 'v_)
(fact 'zz-add-closed 'u_ '(- v_))
(have! '(AND (IN u_ ZZ) (IN (- v_) ZZ)))
(detach! '(IMPLIES (AND (IN u_ ZZ) (IN (- v_) ZZ)) (IN (+ u_ (- v_)) ZZ)))
(ass)
(qed 'zz-sub-in-zz)
(topic! 'zz-sub-in-zz 'plumbing)

;;; rr-add-in-rr / rr-mul-in-rr: the CURRIED closure laws.
;;;
;;; `rr-add-closed' and `rr-mul-closed' (number-systems.scm) state their
;;; hypotheses as an AND, which neither `fact' nor `inst+' will split, so every
;;; citation must be preceded by a `have!' of the conjunction.  That is merely
;;; tedious until the two arguments are the SAME term, at which point the
;;; `have!' of `(AND P P)' is refused as an alpha self-loop -- the claim counts
;;; as already in context -- and a driver needing `t * t in RR' has no move.
;;; These are the same facts with the antecedents curried, so `fact' detaches
;;; each guard on its own and the AND never appears.  (`bt-add-in-carr'
;;; binomial.scm does exactly this for a general ring, and says so.)
(sp (make-wff (forall-guarded '(a_ b_) (list '(IN a_ RR) '(IN b_ RR))
                              '(IN (+ a_ b_) RR))))
(di) (di) (di)
(have! '(AND (IN a_ RR) (IN b_ RR)))
(fact 'rr-add-closed 'a_ 'b_)
(ass)
(qed 'rr-add-in-rr)
(topic! 'rr-add-in-rr 'plumbing)

(sp (make-wff (forall-guarded '(a_ b_) (list '(IN a_ RR) '(IN b_ RR))
                              '(IN (* a_ b_) RR))))
(di) (di) (di)
(have! '(AND (IN a_ RR) (IN b_ RR)))
(fact 'rr-mul-closed 'a_ 'b_)
(ass)
(qed 'rr-mul-in-rr)
(topic! 'rr-mul-in-rr 'plumbing)
