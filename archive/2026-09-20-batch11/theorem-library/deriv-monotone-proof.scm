;;; theorem-library/deriv-monotone-proof.scm -- increasing function theorem.
;;;   f continuous on [a,b], f' > 0 on (a,b)  =>  f strictly increasing on [a,b].
;;; Strategy: for u<v in [a,b], MVT on [u,v] gives theta with
;;;   f(v)-f(u) = f'(theta)(v-u);  f'(theta) > 0 and v-u > 0, so f(v)-f(u) > 0.
;;; Mirrors deriv-zero-const-up (the f'=0 ordered lemma) with a sign in place of
;;; the equality.  Reuses deriv-constant-proof's global dc-* helpers; loads after
;;; mvt-proof.  Uses `fact 'mvt' (no bc*), so it compiles.
;;; ====================================================================

;;; --- warranted supports (curried; forward `fact' detaches each premise) ---
;;; rr-prod-pos RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-rr-order-leaves.scm

;; rr-lt-from-diff-pos is asserted ONCE, in theorem-library/nn-integral.scm; until
;; 2026-09-16 this file asserted it a second time.

;;; ====================================================================
;;; deriv-pos-strictly-increasing:  u<v in [a,b]  =>  f(u) < f(v).
;;; ====================================================================
(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< a x) (< x b)))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (< 0 L)))))
       (FORALL u (FORALL v (IMPLIES (AND (IN u (CCINT a b)) (AND (IN v (CCINT a b)) (< u v)))
         (< (f u) (f v))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)(di)(di)))   ; f,a,b,TYP,CONT,DPOS,u,v,bodyAND
(dc-split)
(define GOAL (dc-gf))
(define CONTHYP (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define DPOSHYP (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

;;; u,v in RR + bounds
(mac-h 'ccint-membership '(IN u (CCINT a b)))
(dc-split)
(mac-h 'ccint-membership '(IN v (CCINT a b)))
(dc-split)
(dc-focus! GOAL)

;;; H1: typing AND for [u,v]
(define H1 '(AND (IN f (FUN RR RR)) (AND (IN u RR) (AND (IN v RR) (< u v)))))
(cut H1) (dc-grind!) (dc-focus! GOAL)

;;; H2: f continuous on [u,v]
(define H2 '(FORALL x (IMPLIES (IN x (CCINT u v)) (IS-CONTINUOUS-AT RR-MS RR-MS f x))))
(cut H2)
(di) (di)
(define H2GOAL (dc-gf))
(mac-h 'ccint-membership '(IN x (CCINT u v)))
(dc-split)
(quietly (lambda () (fact 'rr-le-trans-c 'a 'u 'x)))   ; <= a x
(quietly (lambda () (fact 'rr-le-trans-c 'x 'v 'b)))   ; <= x b
(cut '(IN x (CCINT a b)))
(mac 'ccint-membership) (dc-grind!)
(dc-focus! H2GOAL)
(quietly (lambda () (inst+ CONTHYP 'x) (ass-all)))
(dc-focus! GOAL)

;;; H3: f differentiable on (u,v) -- weaken DPOS (drop the 0<L conjunct)
(define H3 '(FORALL x (IMPLIES (AND (IN x RR) (AND (< u x) (< x v))) (FORSOME L (IS-DIFF-AT f x L)))))
(cut H3)
(di) (di)                                 ; x ; (AND (IN x RR)(AND (< u x)(< x v)))
(dc-split)                                ; IN x RR, < u x, < x v
(define H3GOAL (dc-gf))
(cut '(AND (<= a u) (< u x))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (fact 'rr-le-lt-trans 'a 'u 'x)))   ; < a x
(cut '(AND (< x v) (<= v b))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (fact 'rr-lt-le-trans 'x 'v 'b)))   ; < x b
(cut '(AND (IN x RR) (AND (< a x) (< x b)))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (inst+ DPOSHYP 'x)))   ; -> FORSOME L (AND (IS-DIFF-AT f x L)(< 0 L))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(let ((lx (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) 'x)))))))
  (ew lx) (quietly (lambda () (ass-all))))
(dc-focus! GOAL)

;;; ---- apply the proven MVT on [u,v] ----
(quietly (lambda () (fact 'mvt 'f 'u 'v)))
(dc-detach-impl! H1)
(dc-detach-impl! H2)
(dc-detach-impl! H3)

;;; theta, then MVT's witness L
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (dc-ment? '* z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'u) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'v)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define LW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) THETA))))))
(define EQ1 (list '= (list '* LW '(- v u)) '(- (f v) (f u))))
;; (IN theta RR) came out of the MVT existential with the rest of its body.

;;; theta in (a,b)
(cut (list 'AND '(<= a u) (list '< 'u THETA))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'rr-le-lt-trans 'a 'u THETA)))      ; < a theta
(cut (list 'AND (list '< THETA 'v) '(<= v b))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'rr-lt-le-trans THETA 'v 'b)))      ; < theta b

;;; f'(theta) > 0: DPOS at theta -> L' with (< 0 L'); unique -> L=L'
(cut (list 'AND (list 'IN THETA 'RR) (list 'AND (list '< 'a THETA) (list '< THETA 'b)))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (inst+ DPOSHYP THETA)))   ; -> FORSOME L' (AND (IS-DIFF-AT f theta L')(< 0 L'))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define LP (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) THETA) (not (equal? (cadddr z) LW)))))))
(let ((dd (list 'AND (list 'IS-DIFF-AT 'f THETA LW) (list 'IS-DIFF-AT 'f THETA LP))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique 'f THETA LW LP))))   ; (= LW LP)
(cut (list '< 0 LW))
(subst (list '= LW LP))                   ; goal (< 0 LW) -> (< 0 LP)
(quietly (lambda () (ass-all)))
(dc-focus! GOAL)

;;; endgame: 0 < L, 0 < v-u  =>  0 < L(v-u) = f(v)-f(u)  =>  f(u) < f(v)
(quietly (lambda () (fact 'diff-value-real 'f THETA LW)))   ; (IN LW RR) -- skolem, so not in-rr
(dc-have! '(IN (- v u) RR) GOAL)
(dc-have! '(IN (f u) RR) GOAL)
(dc-have! '(IN (f v) RR) GOAL)
(quietly (lambda () (fact 'rr-lt-diff-pos 'u 'v)))          ; (< 0 (- v u))
(quietly (lambda () (fact 'rr-prod-pos LW '(- v u))))       ; (< 0 (* L (- v u)))
;; C2: 0 < f(v)-f(u)
(cut '(< 0 (- (f v) (f u))))
(quietly (lambda () (fact 'eq-symm '(- (f v) (f u)) (list '* LW '(- v u)))))   ; flip EQ1
(subst (list '= '(- (f v) (f u)) (list '* LW '(- v u))))   ; goal -> (< 0 (* L (- v u)))
(quietly (lambda () (ass-all)))
(dc-focus! GOAL)
(quietly (lambda () (fact 'rr-lt-from-diff-pos '(f u) '(f v))))   ; (< 0 (- (f v)(f u))) => (< (f u)(f v))
(quietly (lambda () (ass-all)))
(qed 'deriv-pos-strictly-increasing)

;;; Classic textbook name, for (find-theorem "...") lookup.
(alias! 'deriv-pos-strictly-increasing
  "increasing function theorem" "positive derivative implies strictly increasing")
(topic! 'deriv-pos-strictly-increasing 'analysis)
