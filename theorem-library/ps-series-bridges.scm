;;; ps-series-bridges.scm -- THE THREE PS/SERIES BRIDGES, PROVEN, and the
;;; CONVERGES twin of rr-limit-ptwise-eq that the third one needed.
;;;
;;;   ps-abs-term              |coef(n) x^n| = |coef(n)| |x|^n
;;;   ps-partial-sum-as-series PS-PARTIAL-SUM(coef,x,k) = SERIES-PARTIAL-SUM(term,k)
;;;   rr-converges-ptwise-eq   pointwise-equal sequences converge together
;;;   ps-converges-as-series   PS-CONVERGES-AT(coef,x) iff SERIES-CONVERGES(term)
;;;
;;; All four `modulo 0'; the first, second and fourth retire asserted supports
;;; from power-series.scm with byte-identical statements.  They are the layer
;;; that lets a theorem proved about bare series be USED about a power series --
;;; without them, theorem-library/series-abs-converges.scm cannot reach
;;; `ps-absolute-implies-convergent' at all.
;;;
;;; TWO OF THE THREE REALLY ARE ONE-LINERS, and one is not.
;;;
;;; `ps-partial-sum-as-series' is the pure definitional unfold its warrant
;;; described: both functoids reduce to the SAME `SUM-AG(RR-additive-AG, term, k)',
;;; so after `mac' on each the goal is literally X = X.  The only cost is that
;;; `rfl' carries a DEFINEDNESS guard, so the sum must be typed first
;;; (`sum-ag-rr-in-rr'), which in turn wants the term lambda in FUN(NN,RR).
;;;
;;; `ps-abs-term' is now two citations rather than an induction, because
;;; `rr-abs-power' (|x^n| = |x|^n) was proved on 2026-09-02 in
;;; geometric-series.scm.  Its warrant proposed exactly this and called the
;;; power law "induction on n" -- that induction is done, so the fact is
;;; multiplicativity plus one rewrite.  The rewrite runs the power law
;;; BACKWARDS: the goal carries |x|^n while the rr-abs-mult instance carries
;;; |x^n|, so the equation is flipped with `eq-sym' before `subst'.
;;;
;;; `ps-converges-as-series' is the one that is NOT a one-liner, and the reason
;;; is a real limitation worth recording: **`mac' will not descend into a
;;; VNB-LAMBDA body.**  Both sides of the iff are a CONVERGES of a lambda whose
;;; BODY is the partial sum, and unfolding the two functoids there would make
;;; the two sides textually identical -- but the macetes report "not applicable"
;;; and the lambdas stay distinct.  So the two sequences are related POINTWISE
;;; instead, which is what `rr-converges-ptwise-eq' consumes, once per
;;; direction.  That lemma is the CONVERGES twin of the tree's existing
;;; `rr-limit-ptwise-eq' (which is about CONVERGES-TO, a named limit) and is
;;; generally useful; it is proved here because this is the first customer.
;;;
;;; ITS ONE TRAP, and it is the documented one: `mac-h' REPLACES the assumption
;;; it unfolds, and `rr-limit-ptwise-eq' needs the CONVERGES-TO itself.  So the
;;; limit's typing is read off a side LANE (`have!' + mac-h inside), leaving the
;;; main branch's hypothesis intact -- continuity-transfer.scm's technique.
;;;
;;; WHAT THIS STILL DOES NOT REACH.  `ps-absolute-implies-convergent' remains
;;; asserted.  With these bridges plus `series-abs-converges' the route is open,
;;; but it needs one lemma that does not exist: pointwise-equal TERM sequences
;;; have equal PARTIAL SUMS (`series-partial-sum-ptwise-eq'), an induction on k.
;;; The tree has the family -- series-partial-sum-add-ptwise,
;;; -le-termwise-ptwise, -scale-ptwise -- but not the plain equality one.  It is
;;; needed because bridge 2 instantiated at the abs'd coefficients produces a
;;; term lambda with a redex in its body, and cleaning that up is a pointwise
;;; move on the terms.
;;;
;;; Loads after geometric-series (rr-abs-power), comparison-test-proof
;;; (sum-ag-rr-in-rr, series-partial-sum-in-rr), limit-arithmetic
;;; (rr-limit-ptwise-eq) and power-series (the PS functoids it retires from).

;;; The three PS/series bridges.
(define (br-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 10) (error "br-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))
(define br-term '(VNB-LAMBDA n NN (* (coef n) (power x n))))

;;; --- 3.  |coef(n) x^n| = |coef(n)| |x|^n -----------------------------
(sp (make-wff
     '(FORALL coef (IMPLIES (IN coef (FUN NN RR))
        (FORALL x (IMPLIES (IN x RR)
          (FORALL n (IMPLIES (IN n NN)
            (= (abs (* (coef n) (power x n)))
               (* (abs (coef n)) (power (abs x) n)))))))))))
(br-peel-to! '=)
(fact 'fun-apply-type-c 'coef 'NN 'RR 'n)
(fact 'power-real-closed 'x 'n)
(have! '(AND (IN (coef n) RR) (IN (power x n) RR)))
(fact 'rr-abs-mult '(coef n) '(power x n))
;; the goal carries |x|^n and the rr-abs-mult instance carries |x^n|, so the
;; power law is applied in the direction that walks the GOAL back to it.
(fact 'rr-abs-power 'n 'x)
(fact 'eq-sym '(abs (power x n)) '(power (abs x) n))
(subst '(= (power (abs x) n) (abs (power x n))))
(ass)
(qed 'ps-abs-term)

;;; --- 1.  the power-series partial sum IS the series partial sum -------
(sp (make-wff
     (list 'FORALL 'coef (list 'IMPLIES '(IN coef (FUN NN RR))
       (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
         (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
           (list '= '(PS-PARTIAL-SUM coef x k)
                 (list 'SERIES-PARTIAL-SUM br-term 'k))))))))))
(br-peel-to! '=)
;; `rfl' carries a definedness guard, so the sum has to be TYPED before the two
;; unfolds make the goal X = X.
(have! (list 'IN br-term '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (let ((v (cadr (cadr (cadr (dk-goal))))))     ; (IN (* (coef v) (power x v)) RR) -> v
               (fact 'fun-apply-type-c 'coef 'NN 'RR v)
               (fact 'power-real-closed 'x v)
               (have! (list 'AND (list 'IN (list 'coef v) 'RR)
                            (list 'IN (list 'power 'x v) 'RR)))
               (fact 'rr-mul-closed (list 'coef v) (list 'power 'x v)))
             (ass)))
(fact 'sum-ag-rr-in-rr 'k br-term)
(mac 'ps-partial-sum)
(mac 'series-partial-sum)
(rfl)
(qed 'ps-partial-sum-as-series)

;;; --- the CONVERGES twin of rr-limit-ptwise-eq -------------------------
(define (br-skolem! ex)
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (x) (if (and (pair? x) (eq? (car x) 'AND)) (dk-split! x))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "br-skolem!: nothing fresh" ex) (car fresh)))))

(sp (make-wff
     '(FORALL f (IMPLIES (IN f (FUN NN RR))
        (FORALL h (IMPLIES (IN h (FUN NN RR))
          (IMPLIES (FORALL j_ (IMPLIES (IN j_ NN) (= (h j_) (f j_))))
            (IMPLIES (CONVERGES RR-MS f) (CONVERGES RR-MS h)))))))))
(br-peel-to! 'CONVERGES)
(define br-ex (dk-landed-find (lambda () (mac-h 'converges '(CONVERGES RR-MS f)))
                              (dk-head? 'FORSOME)))
(define br-L (br-skolem! br-ex))
;; `mac-h' REPLACES the assumption it unfolds, and rr-limit-ptwise-eq needs the
;; CONVERGES-TO itself -- so read the limit's typing off a side LANE and leave
;; the main branch's hypothesis intact.
(have! (list 'IN br-L 'RR)
  (lambda ()
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'converges-to (list 'CONVERGES-TO 'RR-MS 'f br-L)))
                (dk-head? 'AND)))
    (slot-h 'PTS (list 'IN br-L '(PTS RR-MS)))
    (ass)))
(fact 'rr-limit-ptwise-eq 'f 'h br-L)
(mac 'converges)
(ew br-L)
(ass)
(qed 'rr-converges-ptwise-eq)


;;; --- 2.  convergence, via the pointwise transfer ----------------------
;;; The two functoid macetes will NOT descend into a VNB-LAMBDA body ("macete
;;; not applicable"), so the two sides cannot be made textually identical the
;;; way the partial sums were.  They agree POINTWISE instead -- which is exactly
;;; what rr-converges-ptwise-eq consumes, in each direction.
(define br-psl '(VNB-LAMBDA k NN (PS-PARTIAL-SUM coef x k)))
(define br-sl  (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM br-term 'k)))

(sp (make-wff
     (list 'FORALL 'coef (list 'IMPLIES '(IN coef (FUN NN RR))
       (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
         (list 'IFF '(PS-CONVERGES-AT coef x)
               (list 'SERIES-CONVERGES br-term))))))))
(br-peel-to! 'IFF)

;; the term sequence, and both partial-sum sequences, as members of FUN(NN,RR)
(have! (list 'IN br-term '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (let ((v (cadr (cadr (cadr (dk-goal))))))
               (fact 'fun-apply-type-c 'coef 'NN 'RR v)
               (fact 'power-real-closed 'x v)
               (have! (list 'AND (list 'IN (list 'coef v) 'RR)
                            (list 'IN (list 'power 'x v) 'RR)))
               (fact 'rr-mul-closed (list 'coef v) (list 'power 'x v)))
             (ass)))
(have! (list 'IN br-sl '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (fact 'series-partial-sum-in-rr (caddr (cadr (dk-goal))) br-term) (ass)))
(have! (list 'IN br-psl '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             ;; goal (IN (PS-PARTIAL-SUM coef x v) RR) -> v is the FOURTH element
             (let ((v (cadddr (cadr (dk-goal)))))
               (fact 'ps-partial-sum-as-series 'coef 'x v)
               (fact 'series-partial-sum-in-rr v br-term)
               ;; rewrite the goal's PS form into the series form already typed
               (subst (list '= (list 'PS-PARTIAL-SUM 'coef 'x v)
                            (list 'SERIES-PARTIAL-SUM br-term v))))
             (ass)))

;; pointwise agreement, in both orientations
(define br-agr-sp
  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
     (list '= (list br-sl 'j_) (list br-psl 'j_)))))
(define br-agr-ps
  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
     (list '= (list br-psl 'j_) (list br-sl 'j_)))))
(have! br-agr-sp
  (lambda () (di) (lam-b)
             (fact 'ps-partial-sum-as-series 'coef 'x 'j_)
             (fact 'eq-sym (list 'PS-PARTIAL-SUM 'coef 'x 'j_)
                   (list 'SERIES-PARTIAL-SUM br-term 'j_))
             (ass)))
(have! br-agr-ps
  (lambda () (di) (lam-b)
             (fact 'ps-partial-sum-as-series 'coef 'x 'j_)
             (ass)))

(for-each
 (lambda (l)
   (dk-focus! l)
   (di)
   (let ((gl (dk-goal)))
     (if (eq? (car gl) 'SERIES-CONVERGES)
         (begin                                   ; PS => SERIES
           (mac-h 'ps-converges-at '(PS-CONVERGES-AT coef x))
           (fact 'rr-converges-ptwise-eq br-psl br-sl)
           (mac 'series-converges)
           (ass))
         (begin                                   ; SERIES => PS
           (mac-h 'series-converges (list 'SERIES-CONVERGES br-term))
           (fact 'rr-converges-ptwise-eq br-sl br-psl)
           (mac 'ps-converges-at)
           (ass)))))
 (dk-opened (lambda () (di))))
(qed 'ps-converges-as-series)

(topic! 'ps-abs-term 'analysis)
(topic! 'ps-partial-sum-as-series 'analysis)
(topic! 'rr-converges-ptwise-eq 'analysis)
(alias! 'rr-converges-ptwise-eq
        "pointwise-equal real sequences converge together")
(topic! 'ps-converges-as-series 'analysis)
(alias! 'ps-converges-as-series "a power series is the series of its terms")
