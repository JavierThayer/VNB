;;; theorem-library/generalized-mvt-proof.scm -- Cauchy MVT (Thm 2.11), PROVEN.
;;;   L*(g(b)-g(a)) = M*(f(b)-f(a))  for some interior theta with f'=L, g'=M.
;;; Strategy: apply Rolle to the auxiliary
;;;     h(z) = f(z)*(g(b)-g(a)) - g(z)*(f(b)-f(a))
;;; which has h(a)=h(b)=f(a)g(b)-g(a)f(b); Rolle gives interior theta with
;;; h'(theta)=0, and h'(theta) = L(g(b)-g(a)) - M(f(b)-f(a)) where L=f'(theta),
;;; M=g'(theta).  Mirrors mvt-proof.scm with g in place of the identity; reuses
;;; deriv-constant-proof's global dc-* helpers.  Loads after deriv-constant-proof
;;; (and mvt-proof, for rolle / derivative-unique).  Uses `fact', no bc*.
;;; ====================================================================

;;; the auxiliary h(z) = f(z)*(g(b)-g(a)) - g(z)*(f(b)-f(a))
(define GAUX '(VNB-LAMBDA z RR (- (* (f z) (- (g b) (g a))) (* (g z) (- (f b) (f a))))))

;;; --- warranted calc-101 supports for GAUX (curried; linear combo of f,g) ---
(add-to-pss 'gmvt-aux-cont
  `(FORALL f (FORALL g (FORALL a (FORALL b (FORALL x
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS f x)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g x)
       (IS-CONTINUOUS-AT RR-MS RR-MS ,GAUX x)))))))))
(warrant! 'gmvt-aux-cont 'reference
  "h = (g(b)-g(a))f - (f(b)-f(a))g is a linear combination of f and g, hence
   continuous wherever both f and g are (calculus.pdf Thm 2.11).")
(category! 'gmvt-aux-cont 'analysis)

(add-to-pss 'gmvt-aux-diff
  `(FORALL f (FORALL g (FORALL a (FORALL b (FORALL x (FORALL L (FORALL M
     (IMPLIES (IS-DIFF-AT f x L)
     (IMPLIES (IS-DIFF-AT g x M)
       (IS-DIFF-AT ,GAUX x (- (* L (- (g b) (g a))) (* M (- (f b) (f a)))))))))))))))
(warrant! 'gmvt-aux-diff 'reference
  "h'(x) = (g(b)-g(a))f'(x) - (f(b)-f(a))g'(x), from deriv-sum/scalar-mult on the
   linear combination h = (g(b)-g(a))f - (f(b)-f(a))g (calculus.pdf Thm 2.11).")
(category! 'gmvt-aux-diff 'analysis)

;;; ====================================================================
(sp '(FORALL f (FORALL g (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN g (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (AND (IS-CONTINUOUS-AT RR-MS RR-MS f x) (IS-CONTINUOUS-AT RR-MS RR-MS g x))))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (AND (FORSOME L (IS-DIFF-AT f x L)) (FORSOME M (IS-DIFF-AT g x M)))))
       (FORSOME theta (AND (< a theta) (AND (< theta b)
         (FORSOME L (FORSOME M (AND (IS-DIFF-AT f theta L)
                                (AND (IS-DIFF-AT g theta M)
           (= (* L (- (g b) (g a))) (* M (- (f b) (f a)))))))))))))))))))
(quietly (lambda () (di)(di)(di)(di)))     ; f,g,a,b
(dc-split)                                  ; typing AND
(quietly (lambda () (di)(di)))             ; cont hyp, diff hyp
(define GOAL (dc-gf))
(define CONTHYP (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define DIFFHYP (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

;;; GAUX in FUN RR RR
(cut (list 'IN GAUX '(FUN RR RR)))
(dk-lam-t!)
(quietly (lambda () (di) (di) (in-rr)))
(dc-focus! GOAL)

;;; (1) GAUX continuous on [a,b]
(define GCONT (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS GAUX 'x))))
(cut GCONT)
(di) (di)
(quietly (lambda () (inst+ CONTHYP 'x)))   ; -> (AND (cont f x)(cont g x))
(dc-split)
(quietly (lambda () (fact 'gmvt-aux-cont 'f 'g 'a 'b 'x) (ass-all)))
(dc-focus! GOAL)

;;; (2) GAUX differentiable on (a,b)
(define GDIFF (list 'FORALL 'x (list 'IMPLIES '(AND (< a x) (< x b))
                (list 'FORSOME 'L (list 'IS-DIFF-AT GAUX 'x 'L)))))
(cut GDIFF)
(di) (di)
(quietly (lambda () (inst+ DIFFHYP 'x)))   ; -> (AND (FORSOME L diff-f)(FORSOME M diff-g))
(dc-split)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'f)))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'g)))))
(let ((lx (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) 'x))))))
      (mx (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'g) (equal? (caddr z) 'x)))))))
  (quietly (lambda () (fact 'gmvt-aux-diff 'f 'g 'a 'b 'x lx mx)))
  (ew (list '- (list '* lx '(- (g b) (g a))) (list '* mx '(- (f b) (f a)))))
  (quietly (lambda () (ass-all))))
(dc-focus! GOAL)

;;; (3) GAUX(a)=GAUX(b)
(dc-have! '(IN (f a) RR) GOAL)
(dc-have! '(IN (f b) RR) GOAL)
(dc-have! '(IN (g a) RR) GOAL)
(dc-have! '(IN (g b) RR) GOAL)
(cut (list '= (list GAUX 'a) (list GAUX 'b)))
(lam-b)
(crs)
(dc-focus! GOAL)

;;; (4) Rolle on GAUX -> theta, GAUX'(theta)=0
(define RTYP (list 'AND (list 'IN GAUX '(FUN RR RR)) (list 'AND '(IN a RR) (list 'AND '(IN b RR) '(< a b)))))
(cut RTYP) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'rolle GAUX 'a 'b)))
(let loop ((n 0))
  (let ((ri (dc-find (lambda (z) (and ((dc-head? 'IMPLIES) z) (dc-ment? 'VNB-LAMBDA z))))))
    (when (and ri (< n 6)) (detach! ri) (loop (+ n 1)))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'VNB-LAMBDA z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define TH (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
              (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'b)))))))))

;;; (5) extract: f'(theta)=L, g'(theta)=M; gmvt-aux-diff gives GAUX'(theta)=MEXPR;
;;;     derivative-unique vs the Rolle 0 gives 0=MEXPR; rr-diff-zero-eq finishes.
(cut (list 'AND (list '< 'a TH) (list '< TH 'b))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (inst+ DIFFHYP TH)))   ; -> (AND (FORSOME L diff-f)(FORSOME M diff-g))
(dc-split)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'f)))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'g)))))
(define LT (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) TH))))))
(define MT (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'g) (equal? (caddr z) TH))))))
(define MEXPR (list '- (list '* LT '(- (g b) (g a))) (list '* MT '(- (f b) (f a)))))
(quietly (lambda () (fact 'diff-value-real 'f TH LT)))   ; (IN LT RR)
(quietly (lambda () (fact 'diff-value-real 'g TH MT)))   ; (IN MT RR)
(quietly (lambda () (fact 'gmvt-aux-diff 'f 'g 'a 'b TH LT MT)))   ; IS-DIFF-AT GAUX theta MEXPR
(let ((dd (list 'AND (list 'IS-DIFF-AT GAUX TH 0) (list 'IS-DIFF-AT GAUX TH MEXPR))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique GAUX TH 0 MEXPR))))   ; (= 0 MEXPR)
;; rr-diff-zero-eq: u=L(g(b)-g(a)), v=M(f(b)-f(a)); 0=(u-v)=MEXPR => u=v.
(dc-have! (list 'IN (list '* LT '(- (g b) (g a))) 'RR) GOAL)
(dc-have! (list 'IN (list '* MT '(- (f b) (f a))) 'RR) GOAL)
(quietly (lambda () (fact 'rr-diff-zero-eq (list '* LT '(- (g b) (g a))) (list '* MT '(- (f b) (f a))))))

;;; finish: ew theta=TH; close < a TH, < TH b; ew L=LT, M=MT; the AND closes.
(ew TH)
(quietly (lambda () (dc-grind!)))
(let ((fl (any-pred (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
            (and (not (sequent-node-grounded? s)) (pair? g) (eq? (car g) 'FORSOME)))) (proof-leaves))))
  (when fl (set-proof-state-focus! *ps* fl)))
(ew LT)
(ew MT)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'generalized-mvt)
