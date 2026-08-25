;;; continuous-antiderivable.scm -- RUNG 3, AND THE INTEGRAL THAT FOLLOWS.
;;;
;;; EVERY CONTINUOUS FUNCTION ON [a,b] IS ANTIDERIVABLE THERE, and hence
;;; C-INT(f,a,b) -- the definite integral of docs/calculus.pdf (64) -- is
;;; DEFINED for every continuous integrand.  The notes do not number this: it is
;;; Corollary 4.17 (the antiderivable functions are closed under uniform limits)
;;; applied to the approximating sequence of Theorem 5.2 / Corollary 5.7.  Both
;;; halves are already proved elsewhere, so NOTHING analytic happens in this
;;; file; it is packaging, and the packaging is four citations and one
;;; re-indexing.
;;;
;;;   antiderivable-uniform-limit      (antiderivable-uniform-limit.scm, Cor 4.17)
;;;   bernstein-uniform-approximation-ccint  (bernstein-ccint.scm, Thm 5.2 on [a,b])
;;;   bernstein-ccint-approximant-antiderivable
;;;                                    (antiderivable-affine-subst.scm)
;;;
;;; THE ONE PLACE THE TWO STATEMENTS DO NOT LINE UP, and the whole cost of the
;;; assembly: `bernstein-ccint-approximant-antiderivable' needs n /= 0 (the
;;; Bernstein polynomial of degree 0 has no unit-coordinate antiderivative in
;;; this tree), while `antiderivable-uniform-limit' wants a family indexed by
;;; ALL of NN.  So the family is indexed OFF ZERO --
;;;
;;;     PHI(k)  =  the approximant of degree succ(k),
;;;
;;; -- and the threshold has to travel with the shift.  Theorem 5.2 hands back a
;;; cap_ good for every n_ >= cap_; the goal asks for a threshold n0 good for
;;; every k >= n0, at index succ(k).  Taking n0 = cap_ works because
;;; cap_ <= k <= succ(k), which is `nn-le-succ' plus `nn-le-trans-guarded'.
;;; That is the entire re-index: three citations (nn-succ-closed,
;;; nn-succ-nonzero, nn-le-succ) and one transitivity, no new lemma.
;;;
;;; WHY THE FAMILY IS A VNB-LAMBDA AND NOT A BARE TERM.  Cor 4.17 quantifies
;;; over phifam in FUN(NN, FUN(RR,RR)) -- a SET function -- so the family has to
;;; be a term of that membership, which is what `lam-t' certifies.  Its
;;; pointwise obligation is the approximant's membership in FUN(RR,RR), and the
;;; cheapest route to that is not a typing computation at all: the approximant
;;; is ANTIDERIVABLE, and `antiderivable-fn-in-fun' reads the membership off the
;;; antiderivability we are about to cite anyway.  One `fact', no arithmetic.
;;;
;;; BINDER HYGIENE.  Three nested VNB-LAMBDAs appear here at once -- the family
;;; (binder k_), the approximant (binder x) and the affine map A (binder x_) --
;;; and a VNB-LAMBDA v nested inside a VNB-LAMBDA v is a shadowing binder that
;;; only `case-fold-audit' reports.  The three names are pairwise distinct, and
;;; the approximant/affine pair is spelled exactly as
;;; `bernstein-ccint-approximant-antiderivable' spells it, so that citation
;;; matches on the nose rather than up to alpha.
;;;
;;; Needs antiderivable-affine-subst (bernstein-ccint-approximant-antiderivable),
;;; bernstein-ccint (bernstein-uniform-approximation-ccint),
;;; antiderivable-uniform-limit (Cor 4.17, antiderivable-fn-in-fun) and c-int
;;; (c-int-in-rr, c-int-add, c-int-scale).

;;; ---------------------------------------------------------------------
;;; The terms.  `ru-' = RUNG.
;;; ---------------------------------------------------------------------
(define ru-r   '(recip (- b a)))
(define ru-aff '(VNB-LAMBDA x_ RR (+ a (* (- b a) x_))))   ; A(t) = a + (b-a)t
(define ru-g   (list 'COMPOSE 'f ru-aff))                  ; f o A

;; The degree-n approximant of Theorem 5.2, as a MAP on RR.  Character for
;; character the term `bernstein-ccint-approximant-antiderivable' concludes
;; about.
(define (ru-approx n)
  (list 'VNB-LAMBDA 'x 'RR (list 'BERNSTEIN-POLY ru-g n (list '* '(- x a) ru-r))))

;; ... and the family, re-indexed off zero.
(define ru-phifam (list 'VNB-LAMBDA 'k_ 'NN (ru-approx '(SUCC k_))))

(define (ru-cont-of h)
  (forall-guarded 'x_ '(IN x_ (CCINT a b))
                  (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS h 'x_)))
(define ru-cont (ru-cont-of 'f))
(define ru-abc '(AND (IN a RR) (AND (IN b RR) (< a b))))

;;; ---------------------------------------------------------------------
;;; Driver helpers.
;;; ---------------------------------------------------------------------

;; `quietly' silences `vnb-guard' as well as `show', so a tactic that ERRORS
;; inside it becomes a silent no-op.  Every proof below is followed by this.
(define (ru-check name)
  (if (not (proof-done? *ps*))
      (error "continuous-antiderivable: proof did not close" name
             (expression->string (dk-goal)))))

;; `dk-peel-to!' gives up after 8 peels; the linearity statements have more.
(define (ru-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 20) (error "ru-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

;; `have!' of a formula the context already carries is an alpha self-loop.
(define (ru-need! f) (if (not (member f (dk-asms))) (have! f)))

;; A GUARDED universal goes whole under one `di'; a universal whose antecedent
;; is NOT a typing (here `pos-rr(eps)') peels the quantifier and lands NOTHING,
;; and the antecedent arrives on the next call.  Loop on the LANDING.
(define (ru-di-landed!)
  (let loop ((fuel 4))
    (let ((l (dk-landed* (lambda () (di)))))
      (cond ((pair? l) l)
            ((> fuel 0) (loop (- fuel 1)))
            (else (error "ru-di-landed!: nothing ever landed" (dk-goal)))))))

(define (ru-di-var!) (cadr (car (ru-di-landed!))))

;; ... and `di' does NOT take the whole prefix when the antecedents are a mix of
;; typings and order facts: on
;;   forall k in NN. cap <= k => forall x in RR. x in [a,b] => ESTIMATE
;; it lands ONE antecedent per call, four calls in all.  Peel until the goal is
;; the ESTIMATE and return everything landed on the way, so the eigenvariables
;; are read off the LANDINGS rather than off a counted number of `di's.
(define (ru-peel-collect! head)
  (let loop ((n 0) (acc '()))
    (cond ((eq? (car (dk-goal)) head) (reverse acc))
          ((> n 12) (error "ru-peel-collect!: never reached" head (dk-goal)))
          (else (loop (+ n 1)
                      (append (reverse (dk-landed* (lambda () (di)))) acc))))))

(define (ru-typed-in ls dom)
  (cadr (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'IN) (eq? (caddr z) dom)))
                     ls))))

;; The approximant of degree succ(kv) is antiderivable on [a,b].
(define (ru-approx-antideriv! kv)
  (fact 'nn-succ-closed kv)
  (fact 'nn-succ-nonzero kv)
  (ru-need! ru-abc)
  (fact 'bernstein-ccint-approximant-antiderivable 'f (list 'SUCC kv) 'a 'b))

;;; =====================================================================
;;; continuous-is-antiderivable -- RUNG 3.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(f a b)
     (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR))
     (list 'IMPLIES '(< a b) (list 'IMPLIES ru-cont '(IS-ANTIDERIVABLE f a b))))))
  (ru-peel-to! 'IS-ANTIDERIVABLE)
  (ru-need! ru-abc)

  ;; (1) the family is a member of FUN(NN, FUN(RR,RR)).
  (have! (list 'IN ru-phifam '(FUN NN (FUN RR RR)))
    (lambda ()
      (dk-lam-t!)                     ; sethood of NN discharged for us
      (let ((kv (ru-di-var!)))
        (ru-approx-antideriv! kv)
        (fact 'antiderivable-fn-in-fun (ru-approx (list 'SUCC kv)) 'a 'b)
        (ass))))

  ;; (2) cite Cor 4.17 and READ its two antecedents off the landing, rather
  ;; than rebuilding them: a hand-built copy that differs anywhere matches
  ;; nothing and `detach!' then no-ops silently.
  (let* ((h1  (dk-deepest (lambda ()
                (fact 'antiderivable-uniform-limit ru-phifam 'f 'a 'b))))
         (a1  (cadr h1))                       ; every member is antiderivable
         (a2  (cadr (caddr h1))))              ; ... and they converge uniformly

    ;; (3) every member of the family is antiderivable.
    (have! a1
      (lambda ()
        (let ((kv (ru-di-var!)))
          (lam-b)                              ; PHI(k) -> the approximant
          (ru-approx-antideriv! kv)
          (ass))))
    (let ((h2 (dk-deepest (lambda () (detach! h1)))))

      ;; (4) ... and they converge uniformly.  This is where the re-index is paid.
      (have! a2
        (lambda ()
          (let ((epv (cadr (car (ru-di-landed!)))))
            (begin
              (fact 'bernstein-uniform-approximation-ccint 'f 'a 'b epv)
              (let* ((bod   (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))
                     (parts (dk-landed* (lambda () (dk-split! bod))))
                     (uni   (car (filter (dk-head? 'FORALL) parts)))
                     (cap   (cadr (car (filter (dk-head? 'IN) parts)))))
                ;; n0 := cap_, the threshold Theorem 5.2 handed back.
                (dk-ew-split! cap
                  (lambda () (ass))
                  (lambda ()
                    (let* ((ls (ru-peel-collect! '<=))   ; k, cap_<=k, x, x in [a,b]
                           (kv (ru-typed-in ls 'NN))
                           (xv (ru-typed-in ls 'RR)))
                      (begin
                        (lam-b)                  ; PHI(k) -> approximant
                        (lam-b)                  ; ... applied at x
                        ;; cap_ <= k <= succ(k): the whole cost of the shift.
                        (fact 'nn-succ-closed kv)
                        (fact 'nn-le-succ kv)
                        (fact 'nn-le-trans-guarded cap kv (list 'SUCC kv))
                        ;; `inst+' will NOT detach a conjunctive antecedent, so
                        ;; the AND goes into the context whole.
                        (ru-need! (list 'AND (list 'IN (list 'SUCC kv) 'NN)
                                             (list '<= cap (list 'SUCC kv))))
                        (let ((e1 (dk-deepest
                                    (lambda () (inst+ uni (list 'SUCC kv))))))
                          (dk-deepest (lambda () (inst+ e1 xv))))
                        (ass))))))))))
      (detach! h2)
      (ass)))))
(ru-check 'continuous-is-antiderivable)
(qed 'continuous-is-antiderivable)
(topic! 'continuous-is-antiderivable 'analysis)
(alias! 'continuous-is-antiderivable
        "Corollary 4.17 applied to Theorem 5.2"
        "every continuous function on [a,b] is antiderivable on [a,b]")

;;; =====================================================================
;;; c-int-defined-for-continuous -- THE PAYOFF.  The definite integral of a
;;; continuous integrand is defined.  One citation off rung 3.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(f a b)
     (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR))
     (list 'IMPLIES '(< a b) (list 'IMPLIES ru-cont '(IN (C-INT f a b) RR))))))
  (ru-peel-to! 'IN)
  (fact 'continuous-is-antiderivable 'f 'a 'b)
  (fact 'c-int-in-rr 'f 'a 'b)
  (ass)))
(ru-check 'c-int-defined-for-continuous)
(qed 'c-int-defined-for-continuous)
(topic! 'c-int-defined-for-continuous 'analysis)
(alias! 'c-int-defined-for-continuous
        "the definite integral of a continuous function on [a,b] is a real")

;;; =====================================================================
;;; c-int-value-continuous -- equation (64) with its hypothesis discharged.
;;;
;;; `c-int-value' needs an antiderivative HANDED IN, and says nothing about the
;;; integrand; restating it with a continuity hypothesis added would be strictly
;;; weaker, so that is not what is stated here.  What continuity buys is the
;;; WITNESS: an antiderivative EXISTS, and the integral is its increment.  That
;;; is the fundamental theorem of calculus in the form this tree can state it.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(f a b)
     (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR))
     (list 'IMPLIES '(< a b)
       (list 'IMPLIES ru-cont
         (list 'FORSOME 'g_
           (list 'AND '(IS-ANTIDERIVATIVE g_ f a b)
                      '(= (C-INT f a b) (- (g_ b) (g_ a))))))))))
  (ru-peel-to! 'FORSOME)
  (fact 'continuous-is-antiderivable 'f 'a 'b)
  (mac-h 'is-antiderivable '(IS-ANTIDERIVABLE f a b))
  (let* ((wit (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))
         (gv  (cadr wit)))
    (ew gv)
    (for-each (lambda (nd)
                (dk-focus! nd)
                (if (eq? (car (dk-goal)) '=)
                    (begin (fact 'c-int-value gv 'f 'a 'b) (ass))
                    (ass)))
              (dk-opened (lambda () (di)))))))
(ru-check 'c-int-value-continuous)
(qed 'c-int-value-continuous)
(topic! 'c-int-value-continuous 'analysis)
(alias! 'c-int-value-continuous
        "equation (64) for a continuous integrand"
        "a continuous function on [a,b] HAS an antiderivative, and the integral is its increment")

;;; =====================================================================
;;; Proposition 4.12 / 4.13 with the antiderivability hypothesis DISCHARGED:
;;; linearity of the integral for CONTINUOUS integrands.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(phi psi a b)
     (list '(IN phi (FUN RR RR)) '(IN psi (FUN RR RR)) '(IN a RR) '(IN b RR))
     (list 'IMPLIES '(< a b)
       (list 'IMPLIES (ru-cont-of 'phi)
         (list 'IMPLIES (ru-cont-of 'psi)
           '(= (C-INT (VNB-LAMBDA x RR (+ (phi x) (psi x))) a b)
               (+ (C-INT phi a b) (C-INT psi a b)))))))))
  (ru-peel-to! '=)
  (fact 'continuous-is-antiderivable 'phi 'a 'b)
  (fact 'continuous-is-antiderivable 'psi 'a 'b)
  (fact 'c-int-add 'phi 'psi 'a 'b)
  (ass)))
(ru-check 'c-int-add-continuous)
(qed 'c-int-add-continuous)
(topic! 'c-int-add-continuous 'analysis)
(alias! 'c-int-add-continuous
        "Proposition 4.13 for continuous integrands"
        "the integral of a sum of continuous functions is the sum of the integrals")

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(c phi a b)
     (list '(IN c RR) '(IN phi (FUN RR RR)) '(IN a RR) '(IN b RR))
     (list 'IMPLIES '(< a b)
       (list 'IMPLIES (ru-cont-of 'phi)
         '(= (C-INT (VNB-LAMBDA x RR (* c (phi x))) a b)
             (* c (C-INT phi a b))))))))
  (ru-peel-to! '=)
  (fact 'continuous-is-antiderivable 'phi 'a 'b)
  (fact 'c-int-scale 'c 'phi 'a 'b)
  (ass)))
(ru-check 'c-int-scale-continuous)
(qed 'c-int-scale-continuous)
(topic! 'c-int-scale-continuous 'analysis)
(alias! 'c-int-scale-continuous
        "Proposition 4.12 (scalar) for continuous integrands"
        "the integral of a multiple of a continuous function is the multiple of the integral")
