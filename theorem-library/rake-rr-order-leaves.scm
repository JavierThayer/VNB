;;; theorem-library/rake-rr-order-leaves.scm -- the two asserted order leaves of
;;; `deriv-pos-strictly-increasing', PROVEN.
;;;
;;;   rr-prod-pos           0<x, 0<y  =>  0 < x*y   (REMOVED 2026-09-20: the
;;;                         collapse into rr-mul-pos that this header asked for)
;;;   rr-lt-from-diff-pos   0 < y-x   =>  x < y
;;;
;;; STATEMENTS, copied literally from their declaration sites:
;;;   rr-prod-pos          theorem-library/deriv-monotone-proof.scm:11 (add-to-pss)
;;;   rr-lt-from-diff-pos  theorem-library/nn-integral.scm:125 (support)
;;;
;;; NEITHER had any business being asserted.
;;;
;;;   rr-prod-pos is `rr-mul-pos' (theorem-library/rr-recip-order.scm:85, PROVEN
;;;   modulo 0 from rr-lt-scale-pos + rr-mul-zero + ineq) under a second name and
;;;   with the binders spelled x,y instead of a,b.  One `fact' discharges it.
;;;   The two names should eventually collapse into one; this file is the bridge
;;;   that makes the collapse a rename rather than a proof.
;;;
;;;   rr-lt-from-diff-pos is the strict twin of `rr-le-from-diff-nonneg'
;;;   (theorem-library/rr-order-basics.scm:267), which is proven there by ONE
;;;   `ineq' call after the peel.  Its own warrant text says so ("add x to both
;;;   sides of 0 < y-x and simplify").  The strict form is in exactly the same
;;;   linear fragment -- `<' is `lt' to the oracle and binary `-' is arithmetic
;;;   in shape -- so the same three lines decide it.  `ineq' is a TRUSTED oracle
;;;   and adds no leaf to any bill.
;;;
;;; LOAD WINDOW.  After theorem-library/rr-recip-order (rr-mul-pos) and after
;;; the ineq oracle; before theorem-library/deriv-monotone-proof, the only citer
;;; of either name.  `ineq' and the dk- kit both load early, so nothing here is
;;; late-tactic-bound.

;;; --------------------------------------------------------------------
;;; File-local helpers (the `rol-' prefix; never named like a tactic).

;;; The 1-based indices of the ORDER-SHAPED context assumptions -- what `ineq'
;;; wants.  A non-arithmetic premise is skipped by the oracle rather than fatal,
;;; but an `=' between non-arithmetic terms poisons the call, so filter on shape.
;;; (Same filter as ro-idx in rr-order-basics.scm; that file's copy is local to
;;; its own frame, and two uses do not yet justify a driver-kit entry.)
(define (rol-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (#t (loop (cdr l) (+ i 1) acc)))))

(define (rol-ineq!) (apply ineq (rol-idx)))

;;; --------------------------------------------------------------------
;;; rr-prod-pos -- REMOVED 2026-09-20 (batch 11).  It was one citation of
;;; `rr-mul-pos' (theorem-library/rr-recip-order.scm:85) under a second name,
;;; kept as the bridge the header describes; the collapse the header asked for
;;; has now been made, and its one call site (deriv-monotone-proof) cites
;;; rr-mul-pos directly.

;;; --------------------------------------------------------------------
;;; rr-lt-from-diff-pos -- the oracle's home ground.
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (< 0 (- y x)) (< x y))))))))
(dk-peel!)
(rol-ineq!)
(qed 'rr-lt-from-diff-pos)
(topic! 'rr-lt-from-diff-pos 'inequalities)
