;;; extinf-points.scm -- the NEG-INF mirrors of the theorems proven from pos-inf-above-reals
;;; about the two points at infinity.  Agent EXT-INF, 2026-10-26.
;;; DESTINATION: theorem-library/extinf-points.scm.  Library: analysis (the library of
;;; structure-library/extended-reals, whose vocabulary every statement here uses).
;;;
;;;   neg-inf-not-in-rr-proven   NOT (NEG-INF in RR)           mirror of pos-inf-not-in-rr
;;;                              (rake-infinity-points).  Same statement as the PRIMITIVE
;;;                              stamp `neg-inf-not-in-rr' (extended-reals.scm), which this
;;;                              theorem lets the integrator RETIRE: rename this theorem to
;;;                              `neg-inf-not-in-rr' when the stamp goes.
;;;   neg-inf-neq-pos-inf        NOT (NEG-INF = POS-INF)       mirror of pos-inf-neq-neg-inf,
;;;                              by the mirrored route (pos-inf-upper-bound at 0 and the new
;;;                              axiom), not by symmetry of the old one.
;;;   neg-inf-lt-rr              x in RR => NEG-INF < x         mirror of rr-lt-pos-inf
;;;                              (theorem-library/lp-inequalities).
;;;
;;; THE ROUTE of neg-inf-not-in-rr-proven: assume NEG-INF in RR; `neg-inf-below-reals' at
;;; x := NEG-INF gives NOT (NEG-INF <= NEG-INF), `rr-leq-reflexive' at the same term gives
;;; NEG-INF <= NEG-INF.  Both instantiations are licensed by the assumption itself.
;;;
;;; CITATIONS: neg-inf-below-reals (the new primitive, extended-reals.scm), rr-leq-reflexive,
;;; rr-zero-in (number-systems), rr-star-membership, pos-inf-upper-bound, neg-inf-lower-bound
;;; (extended-reals).  Tactics: prop, driver-kit.
;;; LOAD WINDOW: right after theorem-library/rake-infinity-points (no citation is later than
;;; `prop'); before extinf-semigroups.scm, which cites neg-inf-not-in-rr-proven.
;;; Helper prefix: eip-.

(define (eip-in-rr-star! tm keeper)
  (dk-have! (list 'IN tm 'RR-STAR)
    (lambda ()
      (let ((inst (dk-cite! 'rr-star-membership tm)))
        (if (dk-only! inst keeper) (prop))))))

;;; ---------------------------------------------------------------------------
;;; CUT 2026-10-27 (integration): the proof of `neg-inf-not-in-rr-proven' that stood here.  The
;;; stamp `neg-inf-not-in-rr' is retired and the theorem of that name is proven in
;;; theorem-library/rr-star-order-minimal.scm (which loads before this file); the citations
;;; below were renamed to `neg-inf-not-in-rr' (rename-sym.py).

;;; ---------------------------------------------------------------------------
(sp (make-wff '(NOT (= NEG-INF POS-INF))))
(di)
(fact 'rr-zero-in)                      ; (IN 0 RR)
(eip-in-rr-star! 0 '(IN 0 RR))          ; (IN 0 RR-STAR)
(fact 'pos-inf-upper-bound 0)           ; (<= 0 POS-INF)
(fact 'neg-inf-below-reals 0)           ; (NOT (<= 0 NEG-INF))
(dk-have! '(<= 0 NEG-INF)
  (lambda ()
    (subst '(= NEG-INF POS-INF))
    (ass)))
(ai '(NOT (<= 0 NEG-INF)))
(qed 'neg-inf-neq-pos-inf)
(topic! 'neg-inf-neq-pos-inf 'analysis)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (< NEG-INF x)))))
(let* ((landed (dk-peel!))
       (x (cadr (car (filter (lambda (f) (dk-head-is? f 'IN)) landed)))))
  (mac '<)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (dk-head-is? (dk-goal) '<=)
         (begin
           (eip-in-rr-star! x (list 'IN x 'RR))
           (fact 'neg-inf-lower-bound x)
           (ass))
         (begin
           (di)                           ; (= NEG-INF x) assumed; goal FALSITY
           (dk-have! '(IN NEG-INF RR) (lambda () (subst (list '= 'NEG-INF x)) (ass)))
           (fact 'neg-inf-not-in-rr)
           (ai '(NOT (IN NEG-INF RR))))))
   (dk-opened (lambda () (di)))))
(qed 'neg-inf-lt-rr)
(topic! 'neg-inf-lt-rr 'analysis)
