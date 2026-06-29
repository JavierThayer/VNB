;;; theorem-library/mvt-bounds-proof.scm -- Cor 2.14, MACHINE-PROVEN.
;;;   f' <= M on (a,b)  =>  f(b)-f(a) <= M(b-a)     (mvt-upper-bound)
;;;   m <= f' on (a,b)  =>  m(b-a) <= f(b)-f(a)     (mvt-lower-bound)
;;; Strategy: MVT gives theta with f(b)-f(a) = f'(theta)(b-a) = L(b-a); the
;;; bound on f' at theta (transferred to the MVT witness L via derivative-unique)
;;; scales by (b-a) >= 0.  Loads after deriv-constant-proof.scm and reuses its
;;; global dc-* proof helpers.  Uses `fact 'mvt' (no bc*), so it compiles.
;;; ====================================================================

;;; --- warranted support: scale a <= on the RIGHT by a nonneg factor ---
;;; (Curried; rr-le-scale-nonneg is the left-multiply sibling with an AND.)
(add-to-pss 'rr-le-scale-nonneg-right
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (FORALL c (IMPLIES (IN c RR)
       (IMPLIES (<= 0 c) (IMPLIES (<= x y) (<= (* x c) (* y c)))))))))))
(warrant! 'rr-le-scale-nonneg-right 'well-known
  "x<=y and 0<=c give x*c<=y*c (multiply a non-strict inequality on the right by
   a nonnegative factor; the right-multiply form of rr-le-scale-nonneg).")
(category! 'rr-le-scale-nonneg-right 'analysis)

;;; ====================================================================
;;; mvt-upper-bound
;;; ====================================================================
(sp '(FORALL f (FORALL a (FORALL b (FORALL M
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN M RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= L M)))))
       (<= (- (f b) (f a)) (* M (- b a)))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)))   ; f,a,b,M,TYP,CONT,DIFFM
(dc-split)                                            ; split TYP
(define UGOAL (dc-gf))
(define UCONT (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define UDIFF (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

;;; H1: typing AND for MVT on [a,b]
(define UH1 '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b)))))
(cut UH1) (dc-grind!) (dc-focus! UGOAL)

;;; H3: f differentiable on (a,b) -- weaken DIFFM (drop the <=M conjunct)
(define UH3 '(FORALL x (IMPLIES (AND (< a x) (< x b)) (FORSOME L (IS-DIFF-AT f x L)))))
(cut UH3)
(di) (di)                                 ; x ; (AND (< a x)(< x b))
(define UH3G (dc-gf))
(quietly (lambda () (inst+ UDIFF 'x)))    ; -> FORSOME L (AND (IS-DIFF-AT f x L)(<= L M))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(let ((lx (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) 'x)))))))
  (ew lx) (quietly (lambda () (ass-all))))
(dc-focus! UGOAL)

;;; ---- apply MVT on [a,b] (continuity hyp = UCONT already in ctx) ----
(quietly (lambda () (fact 'mvt 'f 'a 'b)))
(dc-detach-impl! UH1)
(dc-detach-impl! UCONT)
(dc-detach-impl! UH3)

;;; theta, then MVT's witness L
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (dc-ment? '* z)))))
(dc-split)
(define UTH (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'b)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define ULW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) UTH))))))
(define UEQ1 (list '= (list '* ULW '(- b a)) '(- (f b) (f a))))

;;; bound on f' at theta: DIFFM at theta -> L' with (<= L' M); unique -> L=L'
(cut (list 'AND (list '< 'a UTH) (list '< UTH 'b))) (dc-grind!) (dc-focus! UGOAL)
(quietly (lambda () (inst+ UDIFF UTH)))   ; -> FORSOME L' (AND (IS-DIFF-AT f theta L')(<= L' M))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define ULP (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) UTH) (not (equal? (cadddr z) ULW)))))))
(let ((dd (list 'AND (list 'IS-DIFF-AT 'f UTH ULW) (list 'IS-DIFF-AT 'f UTH ULP))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! UGOAL)
  (quietly (lambda () (fact 'derivative-unique 'f UTH ULW ULP))))   ; (= L L')
;; (<= L M) from (<= L' M)
(cut (list '<= ULW 'M))
(subst (list '= ULW ULP))                 ; goal (<= L M) -> (<= L' M)
(quietly (lambda () (ass-all)))
(dc-focus! UGOAL)

;;; 0 <= b-a  and  L in RR
(dc-have! '(IN (- b a) RR) UGOAL)
(quietly (lambda () (fact 'rr-zero-in)))               ; (IN 0 RR)
(quietly (lambda () (fact 'rr-lt-diff-pos 'a 'b)))     ; (< 0 (- b a))
(quietly (lambda () (fact 'rr-lt-implies-le 0 '(- b a))))   ; (<= 0 (- b a))
(quietly (lambda () (fact 'diff-value-real 'f UTH ULW)))   ; (IN L RR)
;; finish: f(b)-f(a) = L(b-a) <= M(b-a)
(quietly (lambda () (fact 'eq-symm '(- (f b) (f a)) (list '* ULW '(- b a)))))   ; flip UEQ1
(subst (list '= '(- (f b) (f a)) (list '* ULW '(- b a))))   ; goal -> (<= (* L (- b a))(* M (- b a)))
(quietly (lambda () (fact 'rr-le-scale-nonneg-right ULW 'M '(- b a))))   ; (<= (* L (- b a))(* M (- b a)))
(quietly (lambda () (ass-all)))
(qed 'mvt-upper-bound)

;;; ====================================================================
;;; mvt-lower-bound  (symmetric: m <= L, scale up)
;;; ====================================================================
(sp '(FORALL f (FORALL a (FORALL b (FORALL m
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN m RR) (< a b)))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b))
                 (FORSOME L (AND (IS-DIFF-AT f x L) (<= m L)))))
       (<= (* m (- b a)) (- (f b) (f a)))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)))
(dc-split)
(define LGOAL (dc-gf))
(define LCONT (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define LDIFF (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

(define LH1 '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b)))))
(cut LH1) (dc-grind!) (dc-focus! LGOAL)

(define LH3 '(FORALL x (IMPLIES (AND (< a x) (< x b)) (FORSOME L (IS-DIFF-AT f x L)))))
(cut LH3)
(di) (di)
(quietly (lambda () (inst+ LDIFF 'x)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(let ((lx (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) 'x)))))))
  (ew lx) (quietly (lambda () (ass-all))))
(dc-focus! LGOAL)

(quietly (lambda () (fact 'mvt 'f 'a 'b)))
(dc-detach-impl! LH1)
(dc-detach-impl! LCONT)
(dc-detach-impl! LH3)

(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (dc-ment? '* z)))))
(dc-split)
(define LTH (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'b)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define LLW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) LTH))))))
(define LEQ1 (list '= (list '* LLW '(- b a)) '(- (f b) (f a))))

(cut (list 'AND (list '< 'a LTH) (list '< LTH 'b))) (dc-grind!) (dc-focus! LGOAL)
(quietly (lambda () (inst+ LDIFF LTH)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define LLP (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) LTH) (not (equal? (cadddr z) LLW)))))))
(let ((dd (list 'AND (list 'IS-DIFF-AT 'f LTH LLW) (list 'IS-DIFF-AT 'f LTH LLP))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! LGOAL)
  (quietly (lambda () (fact 'derivative-unique 'f LTH LLW LLP))))   ; (= L L')
;; (<= m L) from (<= m L')
(cut (list '<= 'm LLW))
(subst (list '= LLW LLP))                 ; goal (<= m L) -> (<= m L')
(quietly (lambda () (ass-all)))
(dc-focus! LGOAL)

(dc-have! '(IN (- b a) RR) LGOAL)
(quietly (lambda () (fact 'rr-zero-in)))
(quietly (lambda () (fact 'rr-lt-diff-pos 'a 'b)))
(quietly (lambda () (fact 'rr-lt-implies-le 0 '(- b a))))
(quietly (lambda () (fact 'diff-value-real 'f LTH LLW)))
;; finish: m(b-a) <= L(b-a) = f(b)-f(a)
(quietly (lambda () (fact 'eq-symm '(- (f b) (f a)) (list '* LLW '(- b a)))))   ; flip LEQ1
(subst (list '= '(- (f b) (f a)) (list '* LLW '(- b a))))   ; goal -> (<= (* m (- b a))(* L (- b a)))
(quietly (lambda () (fact 'rr-le-scale-nonneg-right 'm LLW '(- b a))))   ; (<= (* m (- b a))(* L (- b a)))
(quietly (lambda () (ass-all)))
(qed 'mvt-lower-bound)
