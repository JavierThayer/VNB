;;; rr-order-bundle.scm -- four elementary real-order facts, PROVEN modulo 0.
;;;
;;;   rr-prod-nonpos-pos        0 < v  and u*v <= 0   =>  u <= 0
;;;   rr-prod-nonpos-neg        v < 0  and u*v <= 0   =>  0 <= u
;;;   rr-midpoint-between       u < v  =>  forsome w in RR. u < w and w < v
;;;   rr-le-scale-nonneg-right  0 <= c  =>  x <= y  =>  x*c <= y*c
;;;
;;; All four were warranted `well-known' supports -- the first two in
;;; structure-library/order-lemmas.scm, the third declared INSIDE
;;; theorem-library/rolle-proof.scm, the fourth INSIDE mvt-bounds-proof.scm --
;;; and every one of them sits in the 84-88-bill mean-value cluster.  The
;;; statements below are the supports' statements, unchanged.
;;;
;;; THE MECHANISM.  None of the four needs a new idea:
;;;
;;;   * The two product-sign facts are NONLINEAR (the oracle sees `u*v' as one
;;;     opaque atom) and both reduce to ONE cancellation already proven --
;;;     rr-nonneg-cancel-pos (rr-order-basics: 0 < c and 0 <= c*d => 0 <= d).
;;;     Feed it the positive factor (v, or -v) and the other factor as d; the
;;;     only bridge is the ring identity v*(-u) = -(u*v) (resp. (-v)*u =
;;;     -(u*v)), which `crs' decides, and then the goal is linear in the atom
;;;     u*v, so `ineq' does the rest.
;;;   * The midpoint is rr-pos-halvable (rr-halving) applied to v - u -- through
;;;     `dk-halve!' (driver-kit), which hands back d with d + d = v - u, d in RR
;;;     and 0 < d already in context -- and w = u + d is the witness.  The two
;;;     strict inequalities are then linear in d, so `ineq' closes them.
;;;   * The right-multiply scaling is rr-le-scale-nonneg (the left-multiply
;;;     form, proven) plus rr-mul-comm on each side, via `subst'.
;;;
;;; LOAD WINDOW [145, 328): the latest citation is rr-pos-halvable
;;; (theorem-library/rr-halving, position 144), so this file must load after
;;; it; the earliest citer of any of the four is interior-extremum-proof
;;; (position 328, rr-prod-nonpos-pos / -neg).  Also needed and earlier:
;;; rr-order-basics 137 (rr-nonneg-cancel-pos, rr-le-scale-nonneg,
;;; rr-lt-diff-pos), pos-rr-bridges (right after it; rr-pos-rr-in-rr and
;;; rr-lt-of-pos-rr, which dk-halve! cites), pos-rr-of-lt 143
;;; (rr-pos-rr-of-lt), binary-minus-laws 131 (rr-sub-in-rr), and the primitive
;;; number-systems axioms.
;;;
;;; Helper prefix: `rob-'.

;;; (dk-peel! and dk-split-all! became dk-peel! and dk-split-all!, and
;;; rob-close-and! is now a closer handed to dk-conj-close! -- driver-kit.scm,
;;; 2026-09-14.  The halving in rr-midpoint-between is `dk-halve!'.)

;;; 1-based indices of the assumptions `ineq' can use: order relations and
;;; equations (every equation in these contexts is between reals), plus the
;;; `IN _ RR' typings that certify their atoms.
(define (rob-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l))
                (or (memq (caar l) '(< <= =))
                    (and (eq? (caar l) 'IN) (eq? (caddr (car l)) 'RR))))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (else (loop (cdr l) (+ i 1) acc)))))
(define (rob-ineq!) (apply ineq (rob-idx)))

;;; Close a goal that is a right-nested AND of typings and order facts: split
;;; to the leaves, `ass' the typings, `ineq' the rest.
(define (rob-close-and!)
  (dk-conj-close!
   (lambda () (if (eq? (car (dk-goal)) 'IN) (ass) (rob-ineq!)))))

;;; ====================================================================
;;; rr-prod-nonpos-pos:  0 < v and u*v <= 0  =>  u <= 0
;;; ====================================================================
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< 0 v) (<= (* u v) 0)) (<= u 0))))))))
(dk-peel!)
(dk-split-all!)
(fact 'rr-zero-in)
(fact 'rr-neg-closed 'u)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-mul-closed 'u 'v)
(have! '(AND (IN v RR) (IN (- u) RR)))
(fact 'rr-mul-closed 'v '(- u))
;; v * (-u) = -(u*v) is a ring identity; -(u*v) >= 0 is linear in the atom u*v.
(have! '(= (* v (- u)) (- (* u v))) (lambda () (crs)))
(have! '(<= 0 (* v (- u)))
       (lambda () (subst '(= (* v (- u)) (- (* u v)))) (rob-ineq!)))
(fact 'rr-nonneg-cancel-pos 'v '(- u))          ; 0 <= -u
(rob-ineq!)
(qed 'rr-prod-nonpos-pos)
(topic! 'rr-prod-nonpos-pos 'inequalities)

;;; ====================================================================
;;; rr-prod-nonpos-neg:  v < 0 and u*v <= 0  =>  0 <= u
;;; ====================================================================
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< v 0) (<= (* u v) 0)) (<= 0 u))))))))
(dk-peel!)
(dk-split-all!)
(fact 'rr-zero-in)
(fact 'rr-neg-closed 'v)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-mul-closed 'u 'v)
(have! '(AND (IN (- v) RR) (IN u RR)))
(fact 'rr-mul-closed '(- v) 'u)
(have! '(< 0 (- v)) (lambda () (rob-ineq!)))
(have! '(= (* (- v) u) (- (* u v))) (lambda () (crs)))
(have! '(<= 0 (* (- v) u))
       (lambda () (subst '(= (* (- v) u) (- (* u v)))) (rob-ineq!)))
(fact 'rr-nonneg-cancel-pos '(- v) 'u)          ; 0 <= u
(ass)
(qed 'rr-prod-nonpos-neg)
(topic! 'rr-prod-nonpos-neg 'inequalities)

;;; ====================================================================
;;; rr-midpoint-between:  u < v  =>  forsome w in RR. u < w and w < v
;;; ====================================================================
(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (FORSOME w (AND (IN w RR) (AND (< u w) (< w v)))))))))))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-sub-in-rr 'v 'u)                      ; v - u in RR
(fact 'rr-lt-diff-pos 'u 'v)                    ; 0 < v - u
(fact 'rr-pos-rr-of-lt '(- v u))                ; POS-RR(v - u)
(define rob-d (dk-halve! '(- v u)))             ; d with POS-RR d, d + d = v - u,
                                                ; d in RR, 0 < d -- all in context
(have! (list 'AND '(IN u RR) (list 'IN rob-d 'RR)))
(fact 'rr-add-closed 'u rob-d)                  ; u + d in RR
(ew (list '+ 'u rob-d))
(rob-close-and!)
(qed 'rr-midpoint-between)
(topic! 'rr-midpoint-between 'inequalities)

;;; ====================================================================
;;; rr-le-scale-nonneg-right:  0 <= c  =>  x <= y  =>  x*c <= y*c
;;; ====================================================================
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL c (IMPLIES (IN c RR)
       (IMPLIES (<= 0 c) (IMPLIES (<= x y) (<= (* x c) (* y c))))))))))))
(dk-peel!)
(have! '(AND (<= 0 c) (<= x y)))
(fact 'rr-le-scale-nonneg 'c 'x 'y)             ; c*x <= c*y
(have! '(AND (IN x RR) (IN c RR)))
(fact 'rr-mul-comm 'x 'c)                       ; x*c = c*x
(have! '(AND (IN y RR) (IN c RR)))
(fact 'rr-mul-comm 'y 'c)                       ; y*c = c*y
(subst '(= (* x c) (* c x)))
(subst '(= (* y c) (* c y)))
(ass)
(qed 'rr-le-scale-nonneg-right)
(topic! 'rr-le-scale-nonneg-right 'analysis)
