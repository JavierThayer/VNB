;;; poly-tail-zero.scm -- "a polynomial is a sequence that is eventually zero".
;;;
;;; THE STATEMENT.  The tree defines a polynomial over A as a finitely-supported
;;; function NN -> CARR(A) (structure-library/polynomial.scm).  A mathematician
;;; says: an element of SQN(CARR A) which vanishes for all sufficiently large
;;; indices.  The two agree, and until this file nothing in the tree said so:
;;;
;;;     f in CARR(POLY(A))   iff   f in SQN(CARR A)  and
;;;                                exists N in NN. forall k in NN. N <= k => f(k) = 0
;;;
;;; The two halves are proved SEPARATELY and then combined, because their bills
;;; are different and a consumer should pay only for the half it uses:
;;;
;;;   poly-tail-zero-fwd   modulo {nn-finite-subset-bounded}
;;;   poly-tail-zero-bwd   modulo {card-subset-nn, nn-le-succ-cases, nn-le-succ,
;;;                                co-le-trans, nn-le-imp-neq-succ}
;;;   poly-tail-zero       the union of the two
;;;
;;; FORWARD is the finiteness direction: the support is a finite subset of NN,
;;; hence bounded (`nn-finite-subset-bounded', theorem-library/subsequence-
;;; principle.scm -- asserted `well-known', and the single leaf of this half).
;;; Past that bound nothing is in the support, and `supp-membership' turns "not
;;; in the support" into "the coefficient is zero".
;;;
;;; BACKWARD is the converse: the support is contained in ORD-SEGMENT(succ N) --
;;; if a coefficient is non-zero its index cannot be >= N -- and a subset of a
;;; finite set is finite (`card-subset-nn', theorem-library/prod-of-sums.scm,
;;; also asserted `well-known').  Four further leaves come in through
;;; `seg-mem-succ-le' (theorem-library/ord-segment-arith.scm), which is the step
;;; from `z <= N' to `z in ORD-SEGMENT(succ N)'.
;;;
;;; The totality step -- from `not(N <= z)' to `z <= N' -- is `rr-le-total'
;;; (PROVEN modulo 0, theorem-library/rr-order-basics.scm) after `nn-in-rr'
;;; carries both indices into RR.  It is NOT an `ineq' step and cannot be:
;;; Fourier-Motzkin will not negate a `<=' premise (rr-order-basics.scm:632
;;; says so at length); totality is an order axiom's business.
;;;
;;; `prop' does the propositional bookkeeping in three places.  It is capped at
;;; 12 distinct atoms (*prop-atom-cap*) and the case split at the end of the
;;; backward inclusion EXCEEDS that cap -- 14 atoms -- so that one is written as
;;; an explicit `use-cases' on the totality disjunction instead.

(define plt-supp '(SUPP a_ NN-ADD-MONOID f_))
(define plt-tail
  '(FORSOME n_ (AND (IN n_ NN)
      (FORALL k_ (IMPLIES (IN k_ NN)
        (IMPLIES (<= n_ k_) (= (f_ k_) (ZERO a_))))))))

;;; Focus each of the two leaves an AND-goal `di' opened, by GOAL, never by the
;;; order dk-opened happens to return.
(define (plt-both! g1 b1 b2)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) g1)) ls)) (b1)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) g1))) ls)) (b2)))

(define (plt-iff! fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'and)) ls)) (fwd)
    (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'and))) ls)) (bwd)))

;;; =====================================================================
;;; FORWARD -- a polynomial vanishes past some index
;;; =====================================================================

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'f_
   (list 'IMPLIES '(IN f_ (CARR (POLY a_))) plt-tail)))))
(di) (di)
(mac-h 'poly-membership '(IN f_ (CARR (POLY a_))))
(dk-split! (list 'AND '(IN f_ (SQN (CARR a_))) (list 'IN (list 'CARD plt-supp) 'NN)))
;; The support is a subset of NN: its members are points of CARR(NN-ADD-MONOID),
;; which IS NN (nn-add-monoid@carr, installed by declare-instance!).
(have! (list 'SUBSET plt-supp 'NN)
  (lambda ()
    (mac 'subset-def) (di)
    (mac-h 'supp-membership (any-pred (dk-head? 'IN) (dk-asms)))
    (slot-h 'CARR (any-pred (dk-head? 'AND) (dk-asms)))
    (prop)))
;; A finite subset of NN is bounded.  Skolemize the bound off what LANDED --
;; never off a guessed eigenvariable name.
(let* ((ex  (dk-fact! 'nn-finite-subset-bounded plt-supp))
       (two (dk-split! (any-pred (dk-head? 'AND) (dk-landed (lambda () (ai ex))))))
       (typ (any-pred (dk-head? 'IN) two))
       (uni (any-pred (dk-head? 'FORALL) two))
       (w   (cadr typ)))
  (ew w)
  (plt-both! (list 'in w 'nn)
    (lambda () (ass))
    (lambda ()
      (dk-landed (lambda () (di)))              ; k_ in NN
      (dk-landed (lambda () (di)))              ; w <= k_
      ;; the bound says k_ is not in the support; the support law says that
      ;; means the coefficient is zero.
      (let ((neg (dk-deepest (lambda () (inst+ uni 'k_)))))
        (mac-h 'supp-membership neg)
        (slot-h 'CARR (any-pred (dk-head? 'NOT) (dk-asms)))
        (prop)))))
(qed 'poly-tail-zero-fwd)
(gloss! 'poly-tail-zero-fwd
  "A polynomial over A vanishes past some index: there is an N in NN with
   f(k) = ZERO(A) for every k >= N.  The finite support is a bounded subset
   of NN.")
(topic! 'poly-tail-zero-fwd 'algebra)

;;; =====================================================================
;;; BACKWARD -- an eventually-zero sequence is a polynomial
;;; =====================================================================

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'f_
   (list 'IMPLIES '(IN f_ (SQN (CARR a_)))
     (list 'IMPLIES plt-tail '(IN f_ (CARR (POLY a_)))))))))
(di) (di)
(let* ((ex  (any-pred (dk-head? 'FORSOME) (dk-asms)))
       (t2  (dk-split! (any-pred (dk-head? 'AND) (dk-landed (lambda () (ai ex))))))
       (typ (any-pred (dk-head? 'IN) t2))
       (uni (any-pred (dk-head? 'FORALL) t2))
       (w   (cadr typ))
       (seg (list 'ORD-SEGMENT (list 'succ w))))
  ;; (A) ORD-SEGMENT(succ N) is a finite set.
  (have! (list 'AND (list 'IN seg 'SET) (list 'IN (list 'CARD seg) 'NN))
    (lambda ()
      (fact 'nn-succ-closed w)
      (fact 'nn-subset-ord (list 'succ w))
      (fact 'ord-segment-is-set (list 'succ w))
      (fact 'card-segment (list 'succ w))
      (plt-both! (list 'in seg 'set)
        (lambda () (ass))
        (lambda () (subst (list '= (list 'CARD seg) (list 'succ w))) (ass)))))
  ;; (B) the support is a set and lies inside that segment.
  (have! (list 'AND (list 'IN plt-supp 'SET)
            (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ plt-supp)
                                    (list 'IN 'z_ seg))))
    (lambda ()
      (plt-both! (list 'in plt-supp 'set)
        (lambda ()
          (have! '(IN (CARR NN-ADD-MONOID) SET)
                 (lambda () (slot 'CARR) (ta 'nn-is-set) (ass)))
          (fact 'supp-in-set 'a_ 'NN-ADD-MONOID 'f_)
          (ass))
        (lambda ()
          (di)
          (mac-h 'supp-membership (any-pred (dk-head? 'IN) (dk-asms)))
          (slot-h 'CARR (any-pred (dk-head? 'AND) (dk-asms)))
          (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
          ;; z_ cannot be past the bound: there the coefficient is zero, and a
          ;; support member's coefficient is not.
          (have! (list 'NOT (list '<= w 'z_))
            (lambda ()
              (di)
              (dk-deepest (lambda () (inst+ uni 'z_)))
              (ai (list 'NOT (list '= '(f_ z_) '(ZERO a_))))))
          (fact 'nn-in-rr 'z_)
          (fact 'nn-in-rr w)
          (fact 'rr-le-total 'z_ w)
          ;; NOT `prop': the context here carries 14 distinct atoms, over
          ;; *prop-atom-cap*.  The disjunction is named and split by hand.
          (use-cases (list (list '<= 'z_ w) (list '<= w 'z_))
            (lambda () (mac 'seg-mem-succ-le) (ass))
            (lambda () (ai (list 'NOT (list '<= w 'z_)))))))))
  ;; A subset of a finite set is finite.
  (fact 'card-subset-nn seg plt-supp)
  (mac 'poly-membership)
  (prop))
(qed 'poly-tail-zero-bwd)
(gloss! 'poly-tail-zero-bwd
  "A sequence in CARR(A) that is zero from some index on is a polynomial: its
   support sits inside an initial segment of NN, so it is finite.")
(topic! 'poly-tail-zero-bwd 'algebra)

;;; =====================================================================
;;; The equivalence
;;; =====================================================================

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'f_
   (list 'IFF '(IN f_ (CARR (POLY a_)))
     (list 'AND '(IN f_ (SQN (CARR a_))) plt-tail))))))
(di)
(plt-iff!
  (lambda ()
    (fact 'poly-tail-zero-fwd 'a_ 'f_)
    (mac-h 'poly-membership '(IN f_ (CARR (POLY a_))))
    (dk-split! (list 'AND '(IN f_ (SQN (CARR a_))) (list 'IN (list 'CARD plt-supp) 'NN)))
    (plt-both! '(in f_ (sqn (carr a_)))
      (lambda () (ass))
      (lambda () (ass))))
  (lambda ()
    (dk-split! (list 'AND '(IN f_ (SQN (CARR a_))) plt-tail))
    (fact 'poly-tail-zero-bwd 'a_ 'f_)
    (ass)))
(qed 'poly-tail-zero)
(gloss! 'poly-tail-zero
  "f is a polynomial over A iff f is a sequence in CARR(A) -- an element of
   SQN(CARR A) -- which is zero for all sufficiently large indices: there is an
   N in NN with f(k) = ZERO(A) whenever N <= k.  The bridge between the tree's
   definition (finitely-supported function NN -> CARR(A)) and the usual reading
   of a polynomial as an eventually-vanishing coefficient sequence.")
(topic! 'poly-tail-zero 'algebra)
