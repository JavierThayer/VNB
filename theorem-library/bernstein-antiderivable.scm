;;; bernstein-antiderivable.scm -- EVERY BERNSTEIN APPROXIMANT IS ANTIDERIVABLE.
;;;
;;; Rung 3 of the integration arc needs the approximants of Theorem 5.2 to be
;;; antiderivable on [a,b].  bernstein-ccint.scm's closing note says why the two
;;; obvious routes do not exist in this tree, and it is worth repeating in one
;;; line: THERE IS NO CLOSED FORM FOR THE BERNSTEIN BASIS HERE.
;;; BERNSTEIN-BASIS(n,x) is COMB-KK(R,x,1-x,n) (binomial.scm), a PASCAL
;;; RECURSION on the degree, and binomial.scm states only that it is a total
;;; ZZ-indexed family and that it vanishes off 0..m.  Nothing says
;;; B_{k,n}(x) = C(n,k) x^k (1-x)^(n-k); there is no C(n,k) in the tree at all.
;;; So "peel the constant C(n,l), leaving x^l (1-x)^(n-l)" is not a move, the
;;; binomial expansion has nothing to expand, and no re-indexing law for
;;; SERIES-PARTIAL-SUM is wanted -- because none is used.
;;;
;;; WHAT IS USED is the recurrence and nothing else:
;;;
;;;     B_{k,succ n}(x)  =  x B_{k-1,n}(x)  +  (1 - x) B_{k,n}(x)
;;;                                                   (`bernstein-basis-succ')
;;;
;;; An induction on n over "B_{k,n} is antiderivable" does NOT close on it: the
;;; antiderivable maps on [a,b] are a VECTOR SPACE, not an algebra, and the step
;;; multiplies by x.  The repair is to strengthen the hypothesis until the
;;; multiplication is inside it,
;;;
;;;     P(n):  for every k in NN and every j in NN,
;;;            x |-> x^j . B_{k,n}(x)  is antiderivable on [a,b],
;;;
;;; whose step is the recurrence multiplied through by x^j,
;;;
;;;     x^j B_{k,succ n}(x)  =  x^(succ j) B_{k-1,n}(x)
;;;                           + x^j B_{k,n}(x)  -  x^(succ j) B_{k,n}(x),
;;;
;;; i.e. three instances of P(n) combined by `antiderivable-add' and
;;; `antiderivable-sub'.  P(n) at j = 0 gives B_{k,n} itself.
;;;
;;; THE INDEX RANGES OVER NN, NOT ZZ, and that is a deliberate choice about
;;; which case split the proof pays for.  ZZ has no order in this tree -- no
;;; zz-lt, no trichotomy, no embedding in ORD -- so "k in ZZ and k not in NN
;;; implies k < 0", which a ZZ-indexed P(n) would need at every step, is not
;;; available.  Over NN the same boundary is reached by `nn-zero-or-succ', which
;;; is EXCLUDED MIDDLE plus the successor form and needs no order: at k = 0 the
;;; shifted index k-1 is negative and `bernstein-basis-null' makes the term
;;; vanish, and at k = succ q the induction hypothesis applies at q.  This is
;;; exactly the split `bernstein-basis-nonneg' (bernstein-density.scm) makes,
;;; for exactly the same reason, and NN is all `series-partial-sum-antiderivable'
;;; ever asks of the family index.
;;;
;;; THE ZZ INDEX ARITHMETIC, in full, is three facts and no more: (- k_ 1) is an
;;; integer (`zz-sub-in-zz'), it is NEGATIVE when k_ is 0 (`arith' on 0 - 1 < 0
;;; after `subst'), and it is the natural q when k_ is succ q -- the last proved
;;; here rather than cited, `nn-succ-plus-one' plus one `crs', so that
;;; `bt-succ-minus-1' (a `well-known' support, and the reason
;;; `bernstein-basis-nonneg' bills it) stays out of the bill.
;;;
;;; THE INTEGRAND TRANSFER is what makes any of this writable.  Prop 4.8's
;;; conclusions are about the LITERAL lambda they build -- `x |-> phi(x) +
;;; psi(x)' -- so without `antiderivable-integrand-transfer'
;;; (series-antiderivable.scm) the algebra could only ever conclude about
;;; lambdas it built itself and the induction could not be stated.  There are
;;; three transfers in the step: one for each of the two vanishing/IH cases of
;;; the shifted term, and one to carry the assembled sum onto the goal.
;;;
;;; Needs bernstein-basis (BERNSTEIN-BASIS, bernstein-basis-in-fun),
;;; bernstein-moments (bernstein-basis-succ/-null/-ptwise-in-rr),
;;; bernstein-density (BERNSTEIN-POLY), series-antiderivable
;;; (series-partial-sum-antiderivable, power-antiderivable,
;;; zero-is-antiderivable, antiderivable-integrand-transfer),
;;; antiderivative (antiderivable-add/-scale), antiderivative-transfer
;;; (antiderivable-sub), nn-parity-proof (nn-zero-or-succ, nn-succ-plus-one),
;;; series-linearity (series-partial-sum-in-rr-ptwise) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `ba-' prefix) --------------------

(define (ba-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1))) #t))))

(define (ba-check name)
  (if (not (proof-done? *ps*))
      (error "bernstein-antiderivable: proof did not close" name
             (expression->string (dk-goal)))))

(define (ba-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; beta-reduce the goal to a fixed point.  `lam-b' takes one redex per call and
;; a transfer equation carries between two and five of them.
(define (ba-beta*!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (> n 10) 'stop
          (begin (lam-b) (if (equal? g (dk-goal)) 'done (loop (+ n 1))))))))

;; close a pointwise `==' goal whose two sides are equal as ring terms: `crs'
;; proves the `=' form, `subst' carries it, `qrfl' closes X == X.  The sides are
;; READ OFF THE GOAL rather than rebuilt -- rebuilding them is how a driver's
;; guess at a beta normal form silently stops matching.
;; ORIENTATION IS NOT FREE.  `subst' rewrites EVERY occurrence of its left side,
;; so rewriting L to R when L sits INSIDE R replaces the copy of L in R as well
;; and the goal never becomes X == X.  Rewrite whichever side does not occur in
;; the other; they cannot each occur in the other unless they are equal.
(define (ba-eq-close!)
  (let* ((g (dk-goal)) (l (cadr g)) (r (caddr g)))
    (cond ((equal? l r) (qrfl))
          ((not (dk-contains? r l))
           (have! (list '= l r) (lambda () (crs))) (subst (list '= l r)) (qrfl))
          (else
           (have! (list '= r l) (lambda () (crs))) (subst (list '= r l)) (qrfl)))))

;; peel ONE binder of a context universal and return the instantiated body.
;; `inst+' on a formula the context already holds re-derives it onto the very
;; same sequent (`context-add-assumption' is alpha-idempotent), so nothing lands
;; and a `dk-landed' round it errors; every instance below is therefore taken
;; from a CAPTURED intermediate and each binder is peeled exactly once.
(define (ba-inst! f t) (inst+ f t) (subst-free (quantifier-var f) t (quantifier-body f)))

;;; ---- the shapes ------------------------------------------------------

(define ba-guard '(AND (IN a RR) (AND (IN b RR) (< a b))))
(define ba-zero-lam '(VNB-LAMBDA x RR 0))
(define (ba-pow-lam j) (list 'VNB-LAMBDA 'x 'RR (list 'power 'x j)))

;; x |-> x^j . B_{k,n}(x)
(define (ba-term j k n)
  (list 'VNB-LAMBDA 'x 'RR
        (list '* (list 'power 'x j) (list (list 'BERNSTEIN-BASIS n 'x) k))))

;; x |-> B_{k,n}(x)   and   x |-> c . B_{k,n}(x)
(define (ba-basis-lam k n)
  (list 'VNB-LAMBDA 'x 'RR (list (list 'BERNSTEIN-BASIS n 'x) k)))
(define (ba-scaled-lam c k n)
  (list 'VNB-LAMBDA 'x 'RR (list '* c (list (list 'BERNSTEIN-BASIS n 'x) k))))

(define (ba-inner n)
  (forall-guarded '(a b k_ j_)
    (list ba-guard '(IN k_ NN) '(IN j_ NN))
    (list 'IS-ANTIDERIVABLE (ba-term 'j_ 'k_ n) 'a 'b)))

;; the hypothesis `antiderivable-integrand-transfer' takes: psi agrees with phi
;; at every real
(define (ba-pw-eq psi phi)
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '== (list psi 'x_) (list phi 'x_)))))

;; (IN LAM (FUN RR RR)).  `lam-t' opens TWO leaves -- the pointwise typing and
;; the SETHOOD of the domain -- and a driver expecting one leaves the other open.
(define (ba-in-fun! lam pt)
  (have! (list 'IN lam '(FUN RR RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (car (dk-goal)) 'FORALL)
             (let ((v (ba-di-var!))) (pt v) (ass))
             (begin (fact 'rr-is-set) (ass))))
       (dk-opened (lambda () (lam-t)))))))

(define (ba-basis-real! k n v)
  (fact 'bernstein-basis-ptwise-in-rr n v k))
(define (ba-term-real! j k n v)
  (fact 'power-closed-at j v)
  (ba-basis-real! k n v)
  (fact 'rr-mul-in-rr (list 'power v j) (list (list 'BERNSTEIN-BASIS n v) k)))

;; PHI antiderivable + PSI typed + PSI = PHI pointwise  ==>  PSI antiderivable
(define (ba-transfer! phi psi eqlane)
  (have! (ba-pw-eq psi phi) eqlane)
  (fact 'antiderivable-integrand-transfer phi psi 'a 'b))

;;; =====================================================================
;;; 1.  THE DEGREE-ZERO BASIS.  B_{k,0} = IF k = 0 THEN 1 ELSE 0, read off the
;;; recursion's base clause.  `use-em' on the EQUATION k = 0 then `if-true' /
;;; `if-false': plain excluded middle, and no order on the index anywhere.
;;; =====================================================================

;; `br' is 'true or 'false; `rdg' the macete reading the ring constant as a real
(define (ba-degree-zero! br rdg)
  (ba-peel!)
  ;; COMB-KK is ZZ-indexed (2026-09-15), so the `lam-b' below OWES (IN k_ ZZ);
  ;; without it the beta still fires and the leaf is unclosable -- silent until
  ;; qed.  Both call sites have k_ in NN in context.
  (fact 'nn-subset-zz 'k_)
  (mac 'BERNSTEIN-BASIS) (mac 'comb-kk-zero) (lam-b)
  (let* ((goal (dk-goal))
         (ifterm (cadr goal)))
    (for-each
     (lambda (s)
       (dk-focus! s)
       ;; `if-true' opens the CONDITION as one child and the original goal, with
       ;; the reduction landed, as the other.  Both are headed `=' here, so they
       ;; are told apart by the goal itself, never by the head.
       (if (equal? (dk-goal) goal)
           (begin (subst (list '= ifterm (if (eq? br 'true) (caddr ifterm) (cadddr ifterm))))
                  (mac rdg) (arith))
           (ass)))
     (dk-opened (lambda () (if (eq? br 'true) (if-true ifterm) (if-false ifterm)))))))

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(x_ k_) (list '(IN x_ RR) '(IN k_ NN) '(= k_ 0))
                  '(= ((BERNSTEIN-BASIS 0 x_) k_) 1))))
  (ba-degree-zero! 'true 'rr-scalar-ring-one)))
(ba-check 'bernstein-basis-degree-zero-diag)
(qed 'bernstein-basis-degree-zero-diag)
(topic! 'bernstein-basis-degree-zero-diag 'analysis)
(alias! 'bernstein-basis-degree-zero-diag "B_{0,0}(x) = 1")

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(x_ k_) (list '(IN x_ RR) '(IN k_ NN) '(NOT (= k_ 0)))
                  '(= ((BERNSTEIN-BASIS 0 x_) k_) 0))))
  (ba-degree-zero! 'false 'rr-scalar-ring-zero)))
(ba-check 'bernstein-basis-degree-zero-off)
(qed 'bernstein-basis-degree-zero-off)
(topic! 'bernstein-basis-degree-zero-off 'analysis)
(alias! 'bernstein-basis-degree-zero-off "the degree-zero Bernstein basis vanishes off k = 0")

;;; =====================================================================
;;; 2.  P(n):  x |-> x^j B_{k,n}(x) is antiderivable on [a,b], for every k and j.
;;;
;;; THE GUARD `a < b in RR' IS NEVER SPLIT.  `zero-is-antiderivable',
;;; `power-antiderivable' and the induction hypothesis each carry it as ONE
;;; conjunctive antecedent, and `fact' / `inst+' will not split one: fed the
;;; three conjuncts they land the IMPLICATION, silently.  `dk-split!' is
;;; destructive (`ai' REPLACES the conjunction), so splitting it once early
;;; breaks every later citation, several steps away from where it shows.
;;; =====================================================================

(quietly (lambda ()
 (sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (ba-inner 'n_)))))
 (let* ((br  (use-induction))
        (n   (cdr (assq 'var br)))
        (ihf (cdr (assq 'ih  br))))

  ;; ---- BASE:  B_{k,0} is 1 at k = 0 and 0 elsewhere ------------------
  (dk-focus! (cdr (assq 'base br)))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (have! '(IN 0 NN) (lambda () (arith)))
  (fact 'nn-subset-zz 'k_)
  (let ((gg (ba-term 'j_ 'k_ 0)))
    (ba-in-fun! gg (lambda (v) (ba-term-real! 'j_ 'k_ 0 v)))
    (for-each
     (lambda (s)
       (dk-focus! s)
       (if (member '(= k_ 0) (dk-asms))
           (begin                                   ; x^j . 1
             (fact 'power-antiderivable 'j_ 'a 'b)
             (ba-transfer! (ba-pow-lam 'j_) gg
               (lambda ()
                 (let ((v (ba-di-var!)))
                   (ba-beta*!)
                   (subst (dk-fact! 'bernstein-basis-degree-zero-diag v 'k_))
                   (fact 'power-closed-at 'j_ v)
                   (ba-eq-close!))))
             (ass))
           (begin                                   ; x^j . 0
             (fact 'zero-is-antiderivable 'a 'b)
             (ba-transfer! ba-zero-lam gg
               (lambda ()
                 (let ((v (ba-di-var!)))
                   (ba-beta*!)
                   (subst (dk-fact! 'bernstein-basis-degree-zero-off v 'k_))
                   (fact 'power-closed-at 'j_ v)
                   (ba-eq-close!))))
             (ass))))
     (dk-opened (lambda () (use-em '(= k_ 0))))))

  ;; ---- STEP:  the Pascal recurrence, multiplied through by x^j -------
  (dk-focus! (cdr (assq 'step br)))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'nn-succ-closed 'j_)
  (fact 'nn-succ-closed n)
  (fact 'nn-subset-zz 'k_)
  (fact 'zz-one-in)
  (fact 'zz-sub-in-zz 'k_ 1)
  (let* ((t1 (ba-term '(succ j_) '(- k_ 1) n))     ; x^(j+1) B_{k-1,n}
         (t2 (ba-term 'j_        'k_       n))     ; x^j     B_{k,n}
         (t3 (ba-term '(succ j_) 'k_       n))     ; x^(j+1) B_{k,n}
         (gg (ba-term 'j_ 'k_ (list 'succ n)))
         (f2 (ba-inst! (ba-inst! ihf 'a) 'b))       ; FORALL k_. FORALL j_. ...
         (f3 (ba-inst! f2 'k_)))                    ; FORALL j_. ...
    (ba-inst! f3 'j_)                               ; t2 antiderivable
    (ba-inst! f3 '(succ j_))                        ; t3 antiderivable
    ;; (1) the SHIFTED term.  k-1 is outside NN exactly when k is 0, and there
    ;; the basis vanishes; otherwise k is succ q and the hypothesis reaches q.
    (ba-in-fun! t1 (lambda (v) (ba-term-real! '(succ j_) '(- k_ 1) n v)))
    (have! (list 'IS-ANTIDERIVABLE t1 'a 'b)
      (lambda ()
        (fact 'nn-zero-or-succ 'k_)
        (for-each
         (lambda (s)
           (dk-focus! s)
           (if (member '(= k_ 0) (dk-asms))
               (begin
                 (have! '(< (- k_ 1) 0) (lambda () (subst '(= k_ 0)) (arith)))
                 (fact 'zero-is-antiderivable 'a 'b)
                 (ba-transfer! ba-zero-lam t1
                   (lambda ()
                     (let ((v (ba-di-var!)))
                       (ba-beta*!)
                       (subst (dk-fact! 'bernstein-basis-null n v '(- k_ 1)))
                       (fact 'power-closed-at '(succ j_) v)
                       (ba-eq-close!))))
                 (ass))
               (begin
                 (dk-ai-head! 'FORSOME) (dk-ai-head! 'AND)
                 (let* ((eqn (car (filter (lambda (z)
                                            (and (pair? z) (eq? (car z) '=) (eq? (cadr z) 'k_)
                                                 (pair? (caddr z)) (eq? (car (caddr z)) 'succ)))
                                          (dk-asms))))
                        (q (cadr (caddr eqn))))
                   (fact 'nn-in-rr q)
                   ;; (- k_ 1) = q, PROVED (succ q - 1 = (q+1) - 1 = q) rather
                   ;; than cited from `bt-succ-minus-1', which is `well-known'
                   ;; and would be the whole bill's trust tier.
                   (have! (list '= '(- k_ 1) q)
                     (lambda () (subst eqn)
                                (subst (dk-fact! 'nn-succ-plus-one q))
                                (crs)))
                   (have! '(IN (- k_ 1) NN)
                     (lambda () (subst (list '= '(- k_ 1) q)) (ass)))
                   (ba-inst! (ba-inst! f2 '(- k_ 1)) '(succ j_))
                   (ass)))))
         (dk-opened (lambda () (ai (car (filter (dk-head? 'OR) (dk-asms)))))))))
    ;; (2) the three instances, added and subtracted -- and the transfer that
    ;; carries Prop 4.8's literal lambda onto the goal's.
    (let* ((s12 (cadr (dk-fact! 'antiderivable-add t1 t2 'a 'b)))
           (g   (cadr (dk-fact! 'antiderivable-sub s12 t3 'a 'b))))
      (ba-in-fun! gg (lambda (v) (ba-term-real! 'j_ 'k_ (list 'succ n) v)))
      (ba-transfer! g gg
        (lambda ()
          (let ((v (ba-di-var!)))
            (ba-beta*!)
            (subst (dk-fact! 'bernstein-basis-succ n v 'k_))
            (fact 'rr-subset-cc v)
            (have! (list 'AND (list 'IN v 'CC) '(IN j_ NN)))
            (subst (dk-fact! 'power-succ v 'j_))
            (fact 'power-closed-at 'j_ v)
            (fact 'rr-one-in)
            (ba-basis-real! 'k_ n v)
            (ba-basis-real! '(- k_ 1) n v)
            (ba-eq-close!))))
      (ass))))))
(ba-check 'bernstein-term-antiderivable)
(qed 'bernstein-term-antiderivable)
(topic! 'bernstein-term-antiderivable 'analysis)
(alias! 'bernstein-term-antiderivable
        "x |-> x^j B_{k,n}(x) is antiderivable on every [a,b]")

;;; =====================================================================
;;; 3.  P(n) AT j = 0:  the basis polynomial itself, and a constant multiple of
;;; it.  x^0 = 1 (`power-zero'), so the transfer costs one `crs'.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ k_ a b)
        (list '(IN n_ NN) '(IN k_ NN) ba-guard)
        (list 'IS-ANTIDERIVABLE (ba-basis-lam 'k_ 'n_) 'a 'b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (have! '(IN 0 NN) (lambda () (arith)))
  (fact 'nn-subset-zz 'k_)
  (fact 'bernstein-term-antiderivable 'n_ 'a 'b 'k_ 0)
  (let ((lam (ba-basis-lam 'k_ 'n_)))
    (ba-in-fun! lam (lambda (v) (ba-basis-real! 'k_ 'n_ v)))
    (ba-transfer! (ba-term 0 'k_ 'n_) lam
      (lambda ()
        (let ((v (ba-di-var!)))
          (ba-beta*!)
          (fact 'rr-subset-cc v)
          (subst (dk-fact! 'power-zero v))
          (ba-basis-real! 'k_ 'n_ v)
          (ba-eq-close!))))
    (ass))))
(ba-check 'bernstein-basis-antiderivable)
(qed 'bernstein-basis-antiderivable)
(topic! 'bernstein-basis-antiderivable 'analysis)
(alias! 'bernstein-basis-antiderivable
        "every Bernstein basis polynomial is antiderivable on every [a,b]")

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(c n_ k_ a b)
        (list '(IN c RR) '(IN n_ NN) '(IN k_ NN) ba-guard)
        (list 'IS-ANTIDERIVABLE (ba-scaled-lam 'c 'k_ 'n_) 'a 'b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'nn-subset-zz 'k_)
  (fact 'bernstein-basis-antiderivable 'n_ 'k_ 'a 'b)
  (let ((lam (ba-scaled-lam 'c 'k_ 'n_))
        (sc  (cadr (dk-fact! 'antiderivable-scale 'c (ba-basis-lam 'k_ 'n_) 'a 'b))))
    (ba-in-fun! lam
      (lambda (v) (ba-basis-real! 'k_ 'n_ v)
                  (fact 'rr-mul-in-rr 'c (list (list 'BERNSTEIN-BASIS 'n_ v) 'k_))))
    (ba-transfer! sc lam
      (lambda () (ba-di-var!) (ba-beta*!) (qrfl)))
    (ass))))
(ba-check 'bernstein-basis-scaled-antiderivable)
(qed 'bernstein-basis-scaled-antiderivable)
(topic! 'bernstein-basis-scaled-antiderivable 'analysis)
(alias! 'bernstein-basis-scaled-antiderivable
        "a constant multiple of a Bernstein basis polynomial is antiderivable")

;;; =====================================================================
;;; 4.  THE RUNG:  every Bernstein approximant is antiderivable on [a,b].
;;;
;;;   BERNSTEIN-POLY(f,n,x) = SERIES-PARTIAL-SUM(l |-> f(l/n) B_{l,n}(x), succ n)
;;;
;;; so `series-partial-sum-antiderivable' applies with no conversion whatever.
;;; That theorem is STATED IN TRANSFER FORM -- its conclusion is about a map
;;; constrained only by a pointwise `==' to the partial sum, not about the
;;; literal partial-sum lambda -- and that is exactly what a caller whose object
;;; is a `def-functoid' needs: the equation comes from BERNSTEIN-POLY's own
;;; unfold macete and the term never has to be made literally equal to anything.
;;;
;;; n /= 0 IS REQUIRED, and it is not bookkeeping: `/' is `binary-divide-def',
;;; a . recip(b), and recip(0) is undefined, so at n = 0 the coefficient f(l/0)
;;; is not a real and `antiderivable-scale' has nothing to scale by.  The
;;; approximants are used at n above a threshold (bernstein-density.scm), so
;;; nothing wants the n = 0 case.
;;; =====================================================================

(define ba-poly-ph '(VNB-LAMBDA x RR (BERNSTEIN-POLY f n_ x)))
(define ba-poly-fam
  '(VNB-LAMBDA l_ NN (VNB-LAMBDA x RR (* (f (/ l_ n_)) ((BERNSTEIN-BASIS n_ x) l_)))))
(define (ba-summand-at v)
  (list 'VNB-LAMBDA 'l_ 'NN
        (list '* '(f (/ l_ n_)) (list (list 'BERNSTEIN-BASIS 'n_ v) 'l_))))

;; everything f(l/n) needs: l/n is a real, hence f(l/n) is
(define (ba-coeff-real! l)
  (fact 'nn-in-rr l)
  (fact 'rr-mul-in-rr l '(recip n_))
  (have! (list 'IN (list '/ l 'n_) 'RR)
    (lambda () (mac 'binary-divide-def) (ass)))
  (fact 'fun-apply-type-c 'f 'RR 'RR (list '/ l 'n_)))

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(f n_ a b)
        (list '(IN f (FUN RR RR)) '(IN n_ NN) '(NOT (= n_ 0)) ba-guard)
        (list 'IS-ANTIDERIVABLE ba-poly-ph 'a 'b))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'nn-succ-closed 'n_)
  (fact 'nn-in-rr 'n_)
  (have! '(AND (IN n_ RR) (NOT (= n_ 0))))
  (fact 'rr-recip-closed 'n_)
  ;; (1) each summand is antiderivable -- one `lam-b' and section 3.
  (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
               (list 'IS-ANTIDERIVABLE (list ba-poly-fam 'j_) 'a 'b)))
    (lambda ()
      (let ((l (ba-di-var!)))
        (ba-beta*!)
        (ba-coeff-real! l)
        (fact 'nn-subset-zz l)
        (fact 'bernstein-basis-scaled-antiderivable (list 'f (list '/ l 'n_)) 'n_ l 'a 'b)
        (ass))))
  ;; (2) the approximant is a map RR -> RR: the partial sum of a pointwise-real
  ;; family is real (`series-partial-sum-in-rr-ptwise'), and RR is a set.
  (ba-in-fun! ba-poly-ph
    (lambda (v)
      (mac 'BERNSTEIN-POLY)
      (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                   (list 'IN (list (ba-summand-at v) 'k_) 'RR)))
        (lambda ()
          (let ((l (ba-di-var!)))
            (lam-b)
            (ba-coeff-real! l)
            (fact 'nn-subset-zz l)
            (ba-basis-real! l 'n_ v)
            (fact 'rr-mul-in-rr (list 'f (list '/ l 'n_))
                                (list (list 'BERNSTEIN-BASIS 'n_ v) l))
            (ass))))
      (fact 'series-partial-sum-in-rr-ptwise '(succ n_) (ba-summand-at v))))
  ;; (3) the transfer hypothesis: BERNSTEIN-POLY's own unfold, with the
  ;; family-of-lambdas summand beta-reduced UNDER the SERIES-PARTIAL-SUM binder
  ;; -- which `lam-b' does, the binder supplying the (IN j_ NN) the redex owes.
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
               (list '== (list ba-poly-ph 'x_)
                     (list 'SERIES-PARTIAL-SUM
                           (list 'VNB-LAMBDA 'j_ 'NN (list (list ba-poly-fam 'j_) 'x_))
                           '(succ n_)))))
    (lambda ()
      (ba-di-var!)
      (lam-b)                            ; ph_(x_) -> BERNSTEIN-POLY(f, n_, x_)
      (mac 'BERNSTEIN-POLY)              ; ... which IS a SERIES-PARTIAL-SUM
      (ba-beta*!)                        ; ... and the summands beta-reduce to its
      (qrfl)))                           ; family, up to the binder's name
  (fact 'series-partial-sum-antiderivable '(succ n_) ba-poly-fam ba-poly-ph 'a 'b)
  (ass)))
(ba-check 'bernstein-poly-antiderivable)
(qed 'bernstein-poly-antiderivable)
(topic! 'bernstein-poly-antiderivable 'analysis)
(alias! 'bernstein-poly-antiderivable
        "every Bernstein approximant is antiderivable on every [a,b]"
        "rung 3(b) of the integration arc")
