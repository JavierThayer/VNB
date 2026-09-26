;;; ord-segment-arith.scm -- the two bridges between segment membership and
;;; arithmetic on NN.
;;;
;;;     n, j in NN   =>   ( j in S(n)       iff  j <  n )
;;;     n, j in NN   =>   ( j in S(succ n)  iff  j <= n )
;;;
;;; WHY.  Finite combinatorics -- pigeonhole, the surgery kit, the finite half
;;; of the CARD plan -- is stated in ORD-SEGMENTs and argued in inequalities,
;;; and before these two the crossing was done by hand at every step: three
;;; primitive ordinal axioms (ord-segment-membership, ord-lt-iff,
;;; ord-le-nn-compat) chained under an (IN n ORD) typing, each time.
;;;
;;; Both are IFFs, so both are live macetes: `mac' turns a segment goal into an
;;; inequality and `mac-h' does the same to a hypothesis.  The first is proven
;;; modulo 0 -- the three axioms it chains are primitive.  The second buys the
;;; DISCRETENESS step (j <= succ n and j /= succ n gives j <= n), which is not
;;; an ordinal fact but an NN one, and so bills the four well-known NN order
;;; supports it cites.

;;; --------------------------------------------------------------------
;;; j in S(n) iff j < n.  ord-segment-membership reads membership as ORD-LT,
;;; ord-lt-iff splits that into ORD-LE with a disequality, and ord-le-nn-compat
;;; brings ORD-LE down to numeric <=; the goal is then A iff A, since `<' is by
;;; definition <= with a disequality.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IFF (IN j_ (ORD-SEGMENT n_)) (< j_ n_))))))))
(di)
(fact 'nn-subset-ord 'n_)
(fact 'nn-subset-ord 'j_)
(mac 'ord-segment-membership)
(mac 'ord-lt-iff)
(mac 'ord-le-nn-compat)
(mac '<)
(for-each
 (lambda (l)
   (dk-focus! l)
   (for-each (lambda (m)
               (dk-focus! m)
               (ai (car (filter (dk-head? 'AND) (dk-asms))))
               (ass))
             (dk-opened (lambda () (di)))))
 (dk-opened (lambda () (di))))
(qed 'seg-mem-lt)
(topic! 'seg-mem-lt 'set-theory)

;;; --------------------------------------------------------------------
;;; j in S(succ n) iff j <= n -- the discrete form, and the one a finite
;;; argument actually reaches for.  Forward is nn-le-succ-cases against the
;;; disequality; backward is nn-le-succ + transitivity for the bound and
;;; nn-le-imp-neq-succ for the disequality.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IFF (IN j_ (ORD-SEGMENT (succ n_))) (<= j_ n_))))))))
(di)
(fact 'nn-succ-closed 'n_)
(mac 'seg-mem-lt)
(mac '<)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) '<=)
       (begin                                   ; j <= succ n, j /= succ n => j <= n
         (di)
         (dk-split! (car (filter (dk-head? 'AND) (dk-asms))))
         (fact 'nn-le-succ-cases 'n_ 'j_)
         (use-cases (list '(<= j_ n_) '(= j_ (succ n_)))
                    (lambda () (ass))
                    (lambda () (ai '(NOT (= j_ (succ n_)))))))
       (for-each (lambda (m)                    ; j <= n => j <= succ n and j /= succ n
                   (dk-focus! m)
                   (fact 'nn-le-succ 'n_)
(fact 'nn-in-rr 'j_) (fact 'nn-in-rr 'n_) (fact 'nn-succ-closed 'n_) (fact 'nn-in-rr '(succ n_))
                   (fact 'rr-le-trans-c 'j_ 'n_ '(succ n_))
                   (fact 'nn-le-imp-neq-succ 'n_ 'j_)
                   (from-context!))
                 (dk-opened (lambda () (di))))))
 (dk-opened (lambda () (di))))
(qed 'seg-mem-succ-le)
(topic! 'seg-mem-succ-le 'set-theory)
