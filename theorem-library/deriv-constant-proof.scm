;;; theorem-library/deriv-constant-proof.scm -- Cor 2.15, MACHINE-PROVEN.
;;;   f continuous on [a,b], f'=0 on (a,b)  =>  f constant on [a,b].
;;; Strategy: for u<v in [a,b], the proven MVT on [u,v] gives an interior theta
;;; with f'(theta)(v-u)=f(v)-f(u); the zero-derivative hypothesis + derivative-
;;; unique force f'(theta)=0, so f(v)=f(u).  The ordered case is the lemma
;;; `deriv-zero-const-up'; the full statement follows by trichotomy on u,v.
;;; Loads after mvt-proof.scm.  Uses `fact 'mvt' (no bc*), so it compiles.
;;;
;;; Mechanics note: `cut' auto-focuses the new lemma subgoal, so we never
;;; re-focus right after a cut.  dc-focus! matches a leaf by its printed form
;;; (expression->string of the RAW sexp -- NOT via make-wff, which has a
;;; decompose-the-focused-leaf side effect).
;;; ====================================================================

;;; --- file-local proof helpers ---
(define (dc-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (dc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (dc-find pred) (let loop ((as (dc-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (dc-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (dc-ment? sym form) (cond ((eq? form sym) #t)
  ((pair? form) (or (dc-ment? sym (car form)) (dc-ment? sym (cdr form)))) (else #f)))
(define (dc-split) (let loop ((n 0)) (let ((a (dc-find (dc-head? 'AND))))
  (cond ((and a (< n 16)) (ai a) (loop (+ n 1))) (else n)))))
(define (dc-focus! raw)   ; focus the leaf whose goal prints the same as `raw'
  (let ((target (expression->string raw)))
    (let loop ((ls (proof-leaves)))
      (cond ((null? ls) (error "dc-focus!: none equal" target))
            ((string=? (expression->string (wff-formula (sequent-node-assertion (car ls)))) target)
             (set-proof-state-focus! *ps* (car ls)) (car ls))
            (else (loop (cdr ls)))))))
(define (dc-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (set-proof-state-focus! *ps* al) (di) (loop (+ g 1))))))
(define (dc-have! mem back)  ; cut a real-membership fact, prove by in-rr, return to `back'
  (cut mem) (in-rr) (dc-focus! back))
(define (dc-detach-impl! ant)   ; detach the ctx IMPLIES whose antecedent prints as `ant'
  (let ((target (expression->string ant)))
    (let loop ((as (dc-asms)))
      (cond ((null? as) (error "dc-detach-impl!: no IMPLIES with antecedent" target))
            ((and (pair? (car as)) (eq? (caar as) 'IMPLIES)
                  (string=? (expression->string (cadr (car as))) target))
             (detach! (car as)))
            (else (loop (cdr as)))))))
(define (dc-open-leaves) (filter (lambda (s) (not (sequent-node-grounded? s))) (proof-leaves)))
(define (dc-dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display " open=")(display (length (dc-open-leaves)))(newline)
  (display ";;;   goal=")(write (expression->string (dc-gf)))(newline)
  (for-each (lambda (s) (display ";;;   OPEN ")(write (expression->string (wff-formula (sequent-node-assertion s))))(newline))
            (dc-open-leaves)))

;;; --- warranted support: trichotomy of the strict order on RR ---
(add-to-pss 'rr-lt-trichotomy
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (OR (< u v) (OR (= u v) (< v u))))))))
(warrant! 'rr-lt-trichotomy 'well-known
  "RR is totally ordered: for u,v in RR exactly one of u<v, u=v, v<u holds.")
(category! 'rr-lt-trichotomy 'analysis)

;;; --- warranted support: a point strictly between two reals is real ---
;;; (Curried, so forward `fact' detaches each premise -- no AND antecedent.)
(add-to-pss 'rr-strict-between-real
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (FORALL x (IMPLIES (< u x) (IMPLIES (< x v) (IN x RR)))))))))
(warrant! 'rr-strict-between-real 'well-known
  "If u<x<v with u,v real then x is real: the strict order on RR only relates
   reals, so an interior point of [u,v] lies in RR.")
(category! 'rr-strict-between-real 'analysis)

;;; ====================================================================
;;; Lemma deriv-zero-const-up:  u<v in [a,b]  =>  f(u)=f(v).
;;; ====================================================================
(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b)) (IS-DIFF-AT f x 0)))
       (FORALL u (FORALL v (IMPLIES (AND (IN u (CCINT a b)) (AND (IN v (CCINT a b)) (< u v)))
         (= (f u) (f v))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)(di)(di)))   ; f,a,b,TYP,CONT,DZ,u,v,bodyAND
(dc-split)
(define GOAL (dc-gf))
(define CONTHYP (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define DZHYP   (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

;;; u,v in RR + bounds (mac-h consumes the CCINT memberships)
(mac-h 'ccint-membership '(IN u (CCINT a b)))   ; -> (AND (IN u RR)(AND (<= a u)(<= u b)))
(dc-split)
(mac-h 'ccint-membership '(IN v (CCINT a b)))
(dc-split)
(dc-focus! GOAL)

;;; H1: typing AND for [u,v]
(define H1 '(AND (IN f (FUN RR RR)) (AND (IN u RR) (AND (IN v RR) (< u v)))))
(cut H1) (dc-grind!) (dc-focus! GOAL)

;;; H2: f continuous on [u,v]
(define H2 '(FORALL x (IMPLIES (IN x (CCINT u v)) (IS-CONTINUOUS-AT RR-MS RR-MS f x))))
(cut H2)                                  ; cut auto-focuses the H2 subgoal
(di) (di)                                 ; x ; (IN x (CCINT u v))   -> goal is-continuous-at f x
(define H2GOAL (dc-gf))
(mac-h 'ccint-membership '(IN x (CCINT u v)))
(dc-split)                                ; IN x RR, <= u x, <= x v
(quietly (lambda () (fact 'rr-le-trans-c 'a 'u 'x)))   ; <= a u, <= u x -> <= a x
(quietly (lambda () (fact 'rr-le-trans-c 'x 'v 'b)))   ; <= x v, <= v b -> <= x b
(cut '(IN x (CCINT a b)))                 ; auto-focus
(mac 'ccint-membership) (dc-grind!)
(dc-focus! H2GOAL)
(quietly (lambda () (inst+ CONTHYP 'x) (ass-all)))
(dc-focus! GOAL)

;;; H3: f differentiable on (u,v)
(define H3 '(FORALL x (IMPLIES (AND (< u x) (< x v)) (FORSOME L (IS-DIFF-AT f x L)))))
(cut H3)
(di) (di)                                 ; x ; (AND (< u x)(< x v)) -> goal FORSOME L ...
(dc-split)                                ; < u x, < x v
(define H3GOAL (dc-gf))
(quietly (lambda () (fact 'rr-strict-between-real 'u 'v 'x)))   ; -> (IN x RR)
(cut '(AND (<= a u) (< u x))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (fact 'rr-le-lt-trans 'a 'u 'x)))   ; -> < a x
(cut '(AND (< x v) (<= v b))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (fact 'rr-lt-le-trans 'x 'v 'b)))   ; -> < x b
(cut '(AND (< a x) (< x b))) (dc-grind!) (dc-focus! H3GOAL)
(quietly (lambda () (inst+ DZHYP 'x)))    ; AND in ctx -> detaches -> (IS-DIFF-AT f x 0)
(ew 0)                                     ; FORSOME L (IS-DIFF-AT f x L)
(quietly (lambda () (ass-all)))
(dc-focus! GOAL)

;;; ---- apply the proven MVT on [u,v] ----
(quietly (lambda () (fact 'mvt 'f 'u 'v)))
(dc-detach-impl! H1)
(dc-detach-impl! H2)
(dc-detach-impl! H3)

;;; existential elimination: theta then L
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z) (dc-ment? '* z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'u) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'v)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define LW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) THETA))))))
(define EQ1 (list '= (list '* LW '(- v u)) '(- (f v) (f u))))
(quietly (lambda () (fact 'rr-strict-between-real 'u 'v THETA)))   ; -> (IN theta RR)

;;; theta in (a,b)
(cut (list 'AND '(<= a u) (list '< 'u THETA))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'rr-le-lt-trans 'a 'u THETA)))      ; < a theta
(cut (list 'AND (list '< THETA 'v) '(<= v b))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'rr-lt-le-trans THETA 'v 'b)))      ; < theta b
(cut (list 'AND (list '< 'a THETA) (list '< THETA 'b))) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (inst+ DZHYP THETA)))                     ; -> (IS-DIFF-AT f theta 0)

;;; derivative-unique:  IS-DIFF-AT f theta LW and IS-DIFF-AT f theta 0  =>  LW = 0
(let ((dd (list 'AND (list 'IS-DIFF-AT 'f THETA LW) (list 'IS-DIFF-AT 'f THETA 0))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique 'f THETA LW 0))))   ; -> (= LW 0)

;;; endgame:  (= LW 0) + EQ1 + ring algebra  =>  (= (f u)(f v))
(dc-have! '(IN (f u) RR) GOAL)
(dc-have! '(IN (f v) RR) GOAL)
;; (* LW (- v u)) = 0
(cut (list '= (list '* LW '(- v u)) 0))
(subst (list '= LW 0))                    ; goal -> (= (* 0 (- v u)) 0)
(crs)
(dc-focus! GOAL)
;; 0 = (f v)-(f u)
(cut '(= 0 (- (f v) (f u))))
(quietly (lambda () (fact 'eq-symm '(- (f v) (f u)) (list '* LW '(- v u)))))   ; (= (- (f v)(f u)) (* LW (- v u)))
(subst (list '= '(- (f v) (f u)) (list '* LW '(- v u))))   ; goal -> (= 0 (* LW (- v u)))
(subst (list '= (list '* LW '(- v u)) 0))                  ; goal -> (= 0 0)
(crs)
(dc-focus! GOAL)
(quietly (lambda () (fact 'rr-diff-zero-eq '(f v) '(f u))))   ; -> (= (f v)(f u))
(dc-focus! GOAL)
(subst '(= (f v) (f u)))                  ; goal (= (f u)(f v)) -> (= (f u)(f u))
(rfl)
(qed 'deriv-zero-const-up)

;;; ====================================================================
;;; Cor 2.15:  deriv-zero-implies-constant -- the full statement.
;;; Trichotomy on u,v: u<v / u=v / v<u, each reduced to the lemma above.
;;; ====================================================================
(define (dc-focus-case! marker)   ; focus the open leaf whose ctx contains `marker'
  (let ((mstr (expression->string marker)))
    (let loop ((ls (proof-leaves)))
      (cond ((null? ls) (error "dc-focus-case!: none" mstr))
            ((and (not (sequent-node-grounded? (car ls)))
                  (any-pred (lambda (a) (string=? (expression->string a) mstr))
                            (map wff-formula (sequent-node-assumptions (car ls)))))
             (set-proof-state-focus! *ps* (car ls)))
            (else (loop (cdr ls)))))))

(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b)) (IS-DIFF-AT f x 0)))
       (FORALL u (FORALL v (IMPLIES (AND (IN u (CCINT a b)) (IN v (CCINT a b)))
         (= (f u) (f v))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)(di)(di)))   ; f,a,b,TYP,CONT,DZ,u,v,bodyAND
(dc-split)                                                    ; split TYP + bodyAND into pieces
(define MGOAL (dc-gf))
(define TYPAND '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b)))))
(define MCONT (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-continuous-at a)))))
(define MDZ   (dc-find (lambda (a) (and ((dc-head? 'FORALL) a) (dc-ment? 'is-diff-at a)))))

;;; u,v in RR (without destroying the CCINT memberships -- the lemma needs them)
(define (dc-rr-of! var back)
  (cut (list 'IN var 'RR))
  (mac-h 'ccint-membership (list 'IN var '(CCINT a b)))
  (dc-split)
  (quietly (lambda () (ass-all)))
  (dc-focus! back))
(dc-rr-of! 'u MGOAL)
(dc-rr-of! 'v MGOAL)

;;; apply the ordered lemma: in the current (case) leaf produce (= (f p)(f q))
(define (dc-up-eq! mkr p q)
  (cut TYPAND) (dc-grind!) (dc-focus-case! mkr)   ; rebuild the typing AND as a single asm
  (cut (list 'AND (list 'IN p '(CCINT a b)) (list 'AND (list 'IN q '(CCINT a b)) (list '< p q))))
  (dc-grind!)
  (dc-focus-case! mkr)
  (quietly (lambda () (fact 'deriv-zero-const-up 'f 'a 'b)))
  (dc-detach-impl! TYPAND)
  (dc-detach-impl! MCONT)
  (dc-detach-impl! MDZ)
  (let ((dfa (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (pair? (caddr z)) (eq? (car (caddr z)) 'FORALL) (dc-ment? '= z))))))
    (quietly (lambda () (inst+ dfa p))))
  (let ((sfa (dc-find (lambda (z) (and ((dc-head? 'FORALL) z) (pair? (caddr z)) (eq? (car (caddr z)) 'IMPLIES) (dc-ment? '= z) (dc-ment? 'ccint z))))))
    (quietly (lambda () (inst+ sfa q))))
  ;; if inst+ did not auto-detach the AND antecedent, do it now
  (let ((imp (dc-find (lambda (z) (and ((dc-head? 'IMPLIES) z) (dc-ment? '= z) (dc-ment? 'ccint z))))))
    (when imp (detach! imp))))

;;; trichotomy split
(quietly (lambda () (fact 'rr-lt-trichotomy 'u 'v)))
(ai (dc-find (lambda (z) ((dc-head? 'OR) z))))                 ; -> case (< u v) | case (OR (= u v)(< v u))
(dc-focus-case! '(OR (= u v) (< v u)))
(ai (dc-find (lambda (z) ((dc-head? 'OR) z))))                 ; -> case (= u v) | case (< v u)

;;; CASE u<v
(dc-focus-case! '(< u v))
(dc-up-eq! '(< u v) 'u 'v)
(quietly (lambda () (ass-all)))

;;; CASE u=v
(dc-focus-case! '(= u v))
(cut '(IN (f v) RR)) (in-rr) (dc-focus-case! '(= u v))   ; definedness for rfl
(subst '(= u v))                          ; goal (= (f u)(f v)) -> (= (f v)(f v))
(rfl)

;;; CASE v<u
(dc-focus-case! '(< v u))
(dc-up-eq! '(< v u) 'v 'u)                 ; -> (= (f v)(f u))
(cut '(IN (f u) RR)) (in-rr) (dc-focus-case! '(< v u))   ; definedness for rfl
(subst '(= (f v) (f u)))                   ; goal (= (f u)(f v)) -> (= (f u)(f u))
(rfl)

(qed 'deriv-zero-implies-constant)
