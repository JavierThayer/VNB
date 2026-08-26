;;; c-int-change-of-variable.scm -- CHANGE OF VARIABLES FOR `C-INT', in the
;;; INCREASING case, docs/calculus.pdf's substitution rule:
;;;
;;;     C-INT( t |-> phi(A(t)) . A'(t),  p, q )  =  C-INT( phi,  A(p), A(q) ).
;;;
;;; THE WHOLE CONTENT IS TWO CITATIONS.  If F is an antiderivative of phi on
;;; [A(p), A(q)], then `deriv-chain' (chain-rule.scm, modulo 0) says
;;;
;;;     (F o A)'(t)  =  F'(A(t)) . A'(t)  =  phi(A(t)) . A'(t)
;;;
;;; at each t of the OPEN (p,q), and `compose-continuous-at' says F o A is
;;; continuous at each t of the CLOSED [p,q]; those are clauses (2)+(3) and (1)
;;; of Definition 4.6, so F o A is an antiderivative of the left-hand integrand
;;; on [p,q].  `c-int-value' (equation (64)) then evaluates BOTH sides to
;;;
;;;     F(A(q)) - F(A(p)),
;;;
;;; the left side through the composite -- `compose-apply' turning
;;; (F o A)(q) into F(A(q)) -- and the right side directly.  No analysis: no
;;; eps, no delta, no Riemann sum, and nothing here knows what an integral is
;;; beyond Def 4.6.
;;;
;;; WHY IT IS RESTRICTED TO THE INCREASING CASE.  `IS-ANTIDERIVATIVE(f,phi,a,b)'
;;; hard-codes `a < b' (antiderivative.scm, deliberately: Prop 4.10 and the MVT
;;; bounds all want it), so `C-INT(phi, A(p), A(q))' can only be WRITTEN when
;;; A(p) < A(q).  That is why the interval hypotheses below are handed in with
;;; A(p), A(q) as the endpoints rather than derived: with A decreasing the image
;;; interval is [A(q), A(p)] and the statement is a different one.  The
;;; decreasing and degenerate cases belong to `C-INT-OR' (c-int-oriented.scm),
;;; whose whole purpose is to say `int_b^a = -int_a^b' and `int_a^a = 0'; the
;;; general oriented substitution rule is that wrapper's job and is NOT stated
;;; here.
;;;
;;; THE INTERVAL BOOKKEEPING IS TWO UNIVERSALS, NOT ONE, and this is the point
;;; `antiderivable-affine-subst' (the affine special case of the same theorem)
;;; worked out first:
;;;
;;;   * A carries the CLOSED [p,q] into the CLOSED [A(p), A(q)]  -- `cv-maps-in';
;;;   * A carries the OPEN  (p,q) into the OPEN  (A(p), A(q))    -- `cv-maps-int'.
;;;
;;; Both are needed and neither implies the other here.  Def 4.6 asks for
;;; continuity on the closed interval and differentiability on the OPEN one, so
;;; the closed containment alone would leave the derivative clause citing F's
;;; own derivative universal at a point that may sit on the boundary, where F's
;;; hypothesis says nothing.  Handing them in rather than deriving them is also
;;; what keeps the lemma from having to know the SIGN of A': nothing below ever
;;; asks whether A is increasing, only that it carries the two intervals in.
;;;
;;; A' IS A MAP, NOT A LAMBDA -- `ader in FUN(RR,RR)' with the derivative clause
;;; reading `IS-DIFF-AT(A, t, A'(t))'.  With `ader' a VARIABLE the integrand
;;;
;;;     PSI  =  VNB-LAMBDA x RR . phi(A(x)) . A'(x)
;;;
;;; holds no lambda inside a lambda, so the single `lam-b' that reduces PSI(t)
;;; in the derivative clause has exactly ONE redex.  Instantiating `ader' at a
;;; VNB-LAMBDA puts a redex under a binder, and that is the trap
;;; antiderivable-affine-subst's header records: `lam-b-h' reduces EVERY redex of
;;; the formula it is handed, and the inner reduction owes its typing in a
;;; context where the outer binder is free -- an open leaf nothing can close,
;;; reported only as "have!: THUNK left the side goal open".  Section 4 is the
;;; exit for a caller in that position.
;;;
;;; WHAT IS PROVED HERE
;;;
;;;   1. `change-of-variable-antiderivative'  -- F o A IS an antiderivative of
;;;      PSI on [p,q].  `modulo 0'.  This is the theorem; 2-4 are packagings.
;;;   2. `change-of-variable-antiderivable'   -- hence PSI is antiderivable
;;;      there, for a caller who wants only that.  `modulo 0'.
;;;   3. `c-int-change-of-variable'           -- the equation, for the literal
;;;      lambda PSI.
;;;   4. `c-int-change-of-variable-transfer'  -- the equation for ANY psi
;;;      constrained by a pointwise `==' to PSI.  Not decoration: it is what a
;;;      caller whose integrand is a term rather than this literal lambda can
;;;      cite at all, and it is one `antiderivative-integrand-transfer'.
;;;
;;; THE BILL.  1 and 2 are `modulo 0'.  3 and 4 bill EXACTLY what `c-int-value'
;;; bills -- the same fifteen leaves, byte for byte -- and nothing more: every
;;; C-INT result in the tree inherits Cor 4.11's debt through equation (64), and
;;; the change of variables adds no leaf of its own.
;;;
;;; FOR THE LOGARITHM.  `log(xy) = log x + log y' substitutes t = x.u, which is
;;; AFFINE, so the affine instance of section 3/4 is all it needs -- the general
;;; A' is free here, not required.  But `antiderivable-affine-subst' does NOT
;;; suffice on its own: it concludes ANTIDERIVABILITY, and the log law is an
;;; equation between integral VALUES.  The value formula is what this file adds.
;;;
;;; Loads after c-int (c-int-value), chain-rule (deriv-chain), continuity-compose
;;; (compose-continuous-at), compose-apply-proof (compose-type, compose-apply),
;;; antiderivative (Def 4.6, antiderivative-map-in-fun), series-antiderivable
;;; (antiderivative-integrand-transfer), equality-basics (eq-sym),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `cv-' prefix) --------------------

(define (cv-check name)
  (if (not (proof-done? *ps*))
      (error "c-int-change-of-variable: proof did not close" name
             (expression->string (dk-goal)))))

;; `dk-peel-to!' gives up after 8 peels; the statements below have ten
;; antecedents apiece.
(define (cv-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 28) (error "cv-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

(define (cv-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; `have!' of a formula the context already carries is a self-loop, and `have!'
;; says so and stops.  Ask first.
(define (cv-need! f) (if (not (member f (dk-asms))) (have! f)))

;; `di' splits a conjunctive GOAL one level per call; Def 4.6 has seven
;; conjuncts, so split every AND leaf to exhaustion.
(define (cv-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;; The universal of Def 4.6 whose CONSEQUENT speaks about the map FN, taken at
;; argument position SLOT of that consequent.  Discriminating on the HEAD alone
;; would not do: the substitution's own hypotheses `cv-cont' and `cv-diff' are
;; universals with the same two consequent heads, about A rather than about F.
(define (cv-univ head slot fn)
  (let ((hit (filter (lambda (z)
                       (and (pair? z) (eq? (car z) 'FORALL)
                            (let ((body (caddr z)))
                              (and (pair? body) (eq? (car body) 'IMPLIES)
                                   (let ((c (caddr body)))
                                     (and (pair? c) (eq? (car c) head)
                                          (> (length c) slot)
                                          (equal? (list-ref c slot) fn)))))))
                     (dk-asms))))
    (if (null? hit) (error "cv-univ: no such universal" head fn) (car hit))))

;;; ---- the shapes ------------------------------------------------------

(define cv-psi '(VNB-LAMBDA x RR (* (phi (amap x)) (ader x))))   ; t |-> phi(A(t)).A'(t)
(define cv-ap  '(amap p_))
(define cv-aq  '(amap q_))

;; A is continuous on the CLOSED [p,q] ...
(define cv-cont
  (forall-guarded 'u_ '(IN u_ (CCINT p_ q_))
                  '(IS-CONTINUOUS-AT RR-MS RR-MS amap u_)))
;; ... and differentiable on the OPEN (p,q), with derivative A'(t) there.
(define cv-diff
  (forall-guarded 'w_ (conjuncts->and (list '(IN w_ RR) '(< p_ w_) '(< w_ q_)))
                  '(IS-DIFF-AT amap w_ (ader w_))))
;; A carries [p,q] into [A(p),A(q)] ...
(define cv-maps-in
  (forall-guarded 'u_ '(IN u_ (CCINT p_ q_))
                  (list 'IN '(amap u_) (list 'CCINT cv-ap cv-aq))))
;; ... and the OPEN (p,q) into the OPEN (A(p),A(q)).  See the header: Def 4.6
;; differentiates on the open interval, so the closed containment does not serve.
(define cv-maps-int
  (forall-guarded 'w_ (conjuncts->and (list '(IN w_ RR) '(< p_ w_) '(< w_ q_)))
                  (conjuncts->and (list (list '< cv-ap '(amap w_))
                                        (list '< '(amap w_) cv-aq)))))

(define cv-hyps
  (list '(IN amap (FUN RR RR)) '(IN ader (FUN RR RR))
        '(IN p_ RR) '(IN q_ RR) '(< p_ q_)))

;; the four interval/regularity hypotheses, in the order every statement takes
;; them (so the `fact' argument lists below all read alike)
(define cv-reg (list cv-cont cv-diff cv-maps-in cv-maps-int))

;;; =====================================================================
;;; 1.  THE THEOREM.  F o A is an antiderivative of PSI on [p,q].
;;;
;;; The witness is written LITERALLY as `compose-type', `compose-apply',
;;; `compose-continuous-at' and `deriv-chain' produce it -- COMPOSE(F, A) -- so
;;; not one pointwise transfer is needed anywhere in this proof.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(fw phi amap ader p_ q_)
      (append cv-hyps
              (cons (list 'IS-ANTIDERIVATIVE 'fw 'phi cv-ap cv-aq) cv-reg))
      (list 'IS-ANTIDERIVATIVE (list 'COMPOSE 'fw 'amap) cv-psi 'p_ 'q_))))
  (cv-peel-to! 'IS-ANTIDERIVATIVE)
  (fact 'rr-is-set)                            ; compose-type's (IN A SET) guard
  ;; F's hypothesis is unfolded DESTRUCTIVELY, and it may be: everything this
  ;; proof needs from it is a conjunct.  The two universals are then taken by
  ;; the map they speak about, never by position.
  (dk-split! (dk-landed-1
    (lambda () (mac-h 'IS-ANTIDERIVATIVE
                      (list 'IS-ANTIDERIVATIVE 'fw 'phi cv-ap cv-aq)))))
  (let ((cv-cf (cv-univ 'IS-CONTINUOUS-AT 3 'fw))
        (cv-df (cv-univ 'IS-DIFF-AT 1 'fw)))
    (cv-need! '(AND (IN amap (FUN RR RR)) (IN fw (FUN RR RR))))
    (fact 'compose-type 'RR 'RR 'RR 'fw 'amap)          ; F o A : RR -> RR

    ;; the integrand is a map RR -> RR.  `lam-t' opens TWO leaves.
    (have! (list 'IN cv-psi '(FUN RR RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (car (dk-goal)) 'FORALL)
               (let ((v (cv-di-var!)))
                 (fact 'fun-apply-type-c 'amap 'RR 'RR v)
                 (fact 'fun-apply-type-c 'phi 'RR 'RR (list 'amap v))
                 (fact 'fun-apply-type-c 'ader 'RR 'RR v)
                 (cv-need! (list 'AND (list 'IN (list 'phi (list 'amap v)) 'RR)
                                       (list 'IN (list 'ader v) 'RR)))
                 (fact 'rr-mul-in-rr (list 'phi (list 'amap v)) (list 'ader v))
                 (ass))
               (begin (fact 'rr-is-set) (ass))))
         (dk-opened (lambda () (lam-t))))))

    (mac 'IS-ANTIDERIVATIVE)
    (cv-split-goal!)
    (for-each
     (lambda (nd)
       (dk-focus! nd)
       (let ((gl (dk-goal)))
         (cond
          ((memq (car gl) '(IN <)) (ass))
          ;; clause (1): continuity on the CLOSED [p,q].  Told from the
          ;; derivative clause by the SHAPE of its antecedent -- a CCINT typing,
          ;; where the derivative clause carries a three-way AND.
          ((eq? (car (cadr (caddr gl))) 'IN)
           (let ((v (cv-di-var!)))
             (inst+ cv-cont v)                          ; A continuous at v
             (inst+ cv-maps-in v)                       ; A(v) in [A(p),A(q)]
             (inst+ cv-cf (list 'amap v))               ; F continuous there
             (fact 'compose-continuous-at 'fw 'amap v)
             (ass)))
          ;; clauses (2)+(3): the derivative on the OPEN (p,q).
          (else
           (di)
           (dk-split! (dk-landed-1 (lambda () (di))))
           (let* ((th (caddr (dk-goal)))
                  (av (list 'amap th))
                  (mv (list 'phi av)))
             ;; `inst+' does not detach a conjunctive antecedent and the split
             ;; above took the guard apart, so the AND goes back first.
             (cv-need! (list 'AND (list 'IN th 'RR)
                             (list 'AND (list '< 'p_ th) (list '< th 'q_))))
             (inst+ cv-diff th)                         ; A'(th) is the derivative
             (dk-split! (dk-deepest (lambda () (inst+ cv-maps-int th))))
             (fact 'fun-apply-type-c 'amap 'RR 'RR th)  ; A(th) in RR
             (cv-need! (list 'AND (list 'IN av 'RR)
                             (list 'AND (list '< cv-ap av) (list '< av cv-aq))))
             (inst+ cv-df av)                           ; F'(A(th)) = phi(A(th))
             (fact 'deriv-chain 'amap 'fw th (list 'ader th) mv)
             ;; PSI(th) -> phi(A(th)).A'(th).  `th' is typed, and PSI holds no
             ;; lambda, so this is the one redex in the goal.
             (lam-b)
             (ass))))))
     (proof-leaves)))))
(cv-check 'change-of-variable-antiderivative)
(qed 'change-of-variable-antiderivative)
(topic! 'change-of-variable-antiderivative 'analysis)
(alias! 'change-of-variable-antiderivative
        "change of variables: F o A is an antiderivative of the substituted integrand"
        "if F' = phi on [A(p),A(q)] then (F o A)' = phi(A(t)).A'(t) on [p,q]")

;;; =====================================================================
;;; 2.  ... hence the substituted integrand is antiderivable on [p,q].
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi amap ader p_ q_)
      (append cv-hyps
              (cons (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq) cv-reg))
      (list 'IS-ANTIDERIVABLE cv-psi 'p_ 'q_))))
  (cv-peel-to! 'IS-ANTIDERIVABLE)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq))
  ;; the eigenvariable is read off the IS-ANTIDERIVATIVE the skolemization
  ;; landed, never off context order.
  (let ((fv (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
    (mac 'IS-ANTIDERIVABLE)
    (ew (list 'COMPOSE fv 'amap))
    (fact 'change-of-variable-antiderivative fv 'phi 'amap 'ader 'p_ 'q_)
    (ass))))
(cv-check 'change-of-variable-antiderivable)
(qed 'change-of-variable-antiderivable)
(topic! 'change-of-variable-antiderivable 'analysis)
(alias! 'change-of-variable-antiderivable
        "the substituted integrand is antiderivable where the integrand is")

;;; =====================================================================
;;; 3.  THE VALUE -- the change of variables formula itself.
;;;
;;; `c-int-value' twice and `compose-apply' twice.  The `subst' of the first
;;; value equation goes onto the GOAL's LEFT side, whose term does not occur in
;;; the right; the right side is then matched by `eq-sym' rather than by a
;;; second rewrite, so no equation is ever rewritten into itself.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi amap ader p_ q_)
      (append cv-hyps
              (cons (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq) cv-reg))
      (list '= (list 'C-INT cv-psi 'p_ 'q_) (list 'C-INT 'phi cv-ap cv-aq)))))
  (cv-peel-to! '=)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq))
  (let* ((fv (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
         (gg (list 'COMPOSE fv 'amap)))
    (fact 'antiderivative-map-in-fun fv 'phi cv-ap cv-aq)
    (fact 'change-of-variable-antiderivative fv 'phi 'amap 'ader 'p_ 'q_)
    (fact 'c-int-value gg cv-psi 'p_ 'q_)               ; equation (64), left
    (fact 'c-int-value fv 'phi cv-ap cv-aq)             ; equation (64), right
    (cv-need! (list 'AND '(IN amap (FUN RR RR)) (list 'IN fv '(FUN RR RR))))
    ;; (F o A)(x) = F(A(x)).  Cited at arity 5 and instantiated, rather than at
    ;; arity 6: the remaining FORALL sits BELOW the conjunctive antecedent.
    (let ((capp (dk-deepest (lambda () (fact 'compose-apply 'RR 'RR 'RR fv 'amap)))))
      (inst+ capp 'q_)
      (inst+ capp 'p_))
    (subst (list '= (list 'C-INT cv-psi 'p_ 'q_)
                    (list '- (list gg 'q_) (list gg 'p_))))
    (subst (list '= (list gg 'q_) (list fv cv-aq)))
    (subst (list '= (list gg 'p_) (list fv cv-ap)))
    (fact 'eq-sym (list 'C-INT 'phi cv-ap cv-aq)
                  (list '- (list fv cv-aq) (list fv cv-ap)))
    (ass))))
(cv-check 'c-int-change-of-variable)
(qed 'c-int-change-of-variable)
(topic! 'c-int-change-of-variable 'analysis)
(alias! 'c-int-change-of-variable
        "change of variables in a definite integral"
        "the integral of phi(A(t)).A'(t) over [p,q] is the integral of phi over [A(p),A(q)]")

;;; =====================================================================
;;; 4.  ... in TRANSFER form.  See the header: this is what lets a caller whose
;;; integrand is a TERM, rather than the literal lambda the statement builds,
;;; cite the theorem at all -- and it is one `antiderivative-integrand-transfer'.
;;; =====================================================================

(define cv-pw
  (forall-guarded 'x_ '(IN x_ RR)
                  (list '== '(psi x_) '(* (phi (amap x_)) (ader x_)))))

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi psi amap ader p_ q_)
      (append cv-hyps
              (cons '(IN psi (FUN RR RR))
                    (cons (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq)
                          (append cv-reg (list cv-pw)))))
      (list '= (list 'C-INT 'psi 'p_ 'q_) (list 'C-INT 'phi cv-ap cv-aq)))))
  (cv-peel-to! '=)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE 'phi cv-ap cv-aq))
  (let* ((fv (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
         (gg (list 'COMPOSE fv 'amap)))
    (fact 'antiderivative-map-in-fun fv 'phi cv-ap cv-aq)
    (fact 'change-of-variable-antiderivative fv 'phi 'amap 'ader 'p_ 'q_)
    ;; psi agrees pointwise with PSI: one goal-side `lam-b' -- PSI applied to a
    ;; TYPED eigenvariable, one redex -- and the hypothesis.
    (have! (forall-guarded 'x_ '(IN x_ RR) (list '== '(psi x_) (list cv-psi 'x_)))
      (lambda ()
        (let ((v (cv-di-var!)))
          (lam-b)
          (inst+ cv-pw v)
          (ass))))
    (fact 'antiderivative-integrand-transfer gg cv-psi 'psi 'p_ 'q_)
    (fact 'c-int-value gg 'psi 'p_ 'q_)
    (fact 'c-int-value fv 'phi cv-ap cv-aq)
    (cv-need! (list 'AND '(IN amap (FUN RR RR)) (list 'IN fv '(FUN RR RR))))
    (let ((capp (dk-deepest (lambda () (fact 'compose-apply 'RR 'RR 'RR fv 'amap)))))
      (inst+ capp 'q_)
      (inst+ capp 'p_))
    (subst (list '= (list 'C-INT 'psi 'p_ 'q_)
                    (list '- (list gg 'q_) (list gg 'p_))))
    (subst (list '= (list gg 'q_) (list fv cv-aq)))
    (subst (list '= (list gg 'p_) (list fv cv-ap)))
    (fact 'eq-sym (list 'C-INT 'phi cv-ap cv-aq)
                  (list '- (list fv cv-aq) (list fv cv-ap)))
    (ass))))
(cv-check 'c-int-change-of-variable-transfer)
(qed 'c-int-change-of-variable-transfer)
(topic! 'c-int-change-of-variable-transfer 'analysis)
(alias! 'c-int-change-of-variable-transfer
        "change of variables, stated for any map agreeing pointwise with the substituted integrand")
