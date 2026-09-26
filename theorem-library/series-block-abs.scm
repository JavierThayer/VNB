;;; series-block-abs.scm -- THE BLOCK TRIANGLE INEQUALITY, in the form a Cauchy
;;; argument can use, and the NN gap lemma under it.
;;;
;;;   series-abs-triangle-block  |S(f,m+d) - S(f,m)| <= S(g,m+d) - S(g,m)
;;;   nn-le-gap                  m <= k  =>  k = m + d for some d in NN
;;;   series-abs-triangle-le     m <= k  =>  |S(f,k) - S(f,m)| <= S(g,k) - S(g,m)
;;;
;;; WHY THREE THEOREMS FOR ONE FACT.  `use-induction' counts from 0, so the
;;; block estimate has to be proved over the GAP -- induct on d with the upper
;;; index m + d -- and that is not the shape a caller has: `series-cauchy-
;;; criterion' and every eps/N argument quantify `bnd <= m <= n'.  Converting
;;; between them is exactly `nn-le-gap', which the tree did not have: no lemma
;;; anywhere said that m <= k produces a d with k = m + d.  It is the standard
;;; induction with `nn-le-succ-cases' at the step, and it is the only reason
;;; this file has three theorems instead of one.
;;;
;;; TRANSFER FORM again -- `g' agrees pointwise with the absolute values rather
;;; than being the literal lambda -- for the reason series-abs-triangle.scm and
;;; cc-series.scm both give.
;;;
;;; THREE MECHANICS worth keeping.
;;;
;;;  * CAPTURE THE AGREEMENT HYPOTHESIS BEFORE ANY CITATION LANDS.  A finder
;;;    reading "the FORALL that mentions `abs'" picks `rr-abs-triangle' the
;;;    moment a `fact' has landed it -- the look-alike trap CLAUDE.md describes,
;;;    met in the flesh.  Taken immediately after the peel, the only universal
;;;    in the context IS the hypothesis.
;;;  * `rfl' CARRIES A DEFINEDNESS GUARD, and its warning names the wrong
;;;    reason.  `pi-reflexivity!' (primitive-inferences.scm:647) closes t = t
;;;    only when t is defined -- syntactically, or by a context (IN t _).
;;;    `succ(m + d)' is neither until the typing lands, and without it the
;;;    warning reads "goal is not (= a a)" about a goal that is visibly
;;;    (= a a).  `qrfl' is not the fix: it wants `==', and this goal is `='.
;;;  * The regroupings -- (S + t) - S0 into (S - S0) + t -- are pure ring
;;;    identities, so they go in by `have!' + `crs' and then `subst'.  `crs'
;;;    cannot be applied to the goal directly: the goal has an `abs' in it, and
;;;    the simplifier declines any identity it cannot read as a ring term.
;;;
;;; WHAT IT COSTS.  The block form is `modulo 0'.  `nn-le-gap' and hence the
;;; usable form bill {nn-not-le-zero-pos}, an asserted NN order support that
;;; arrives through `nn-le-zero-is-zero' in the base case.
;;;
;;; Loads after series-abs-triangle (the un-blocked inequality, same shape),
;;; nn-order-proof / nn-order-ord (nn-le-succ-cases, nn-le-zero-is-zero),
;;; nn-arith (nn-add-succ, nn-add-zero) and driver-kit (`use-cases').

;;; |S(f, m+d) - S(f,m)| <= S(g, m+d) - S(g,m)   -- induction on the GAP d.
(define (bl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bl-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (bl-ineq . fs) (apply ineq (map bl-idx fs)))
(define (bl-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "bl-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff
     '(FORALL d (IMPLIES (IN d NN)
        (FORALL m (IMPLIES (IN m NN)
          (FORALL f (IMPLIES (IN f (FUN NN RR))
            (FORALL g (IMPLIES (IN g (FUN NN RR))
              (IMPLIES (FORALL j (IMPLIES (IN j NN) (= (g j) (abs (f j)))))
                (<= (abs (- (SERIES-PARTIAL-SUM f (+ m d)) (SERIES-PARTIAL-SUM f m)))
                    (- (SERIES-PARTIAL-SUM g (+ m d)) (SERIES-PARTIAL-SUM g m))))))))))))))
(define bl-br (use-induction))

;;; BASE d = 0
(dk-focus! (cdr (assq 'base bl-br)))
(bl-peel-to! '<=)
(mac 'nn-add-zero)
(fact 'series-partial-sum-in-rr 'm 'f)
(fact 'series-partial-sum-in-rr 'm 'g)
(have! '(= (- (SERIES-PARTIAL-SUM f m) (SERIES-PARTIAL-SUM f m)) 0) (lambda () (crs)))
(subst '(= (- (SERIES-PARTIAL-SUM f m) (SERIES-PARTIAL-SUM f m)) 0))
(mac 'rr-abs-zero-value)
(bl-ineq (list 'IN '(SERIES-PARTIAL-SUM g m) 'RR))

;;; STEP
(dk-focus! (cdr (assq 'step bl-br)))
(define bl-d  (cdr (assq 'var bl-br)))
(define bl-ih (cdr (assq 'ih  bl-br)))
;; CAPTURE THE AGREEMENT FIRST.  Discriminating on a symbol later picks up
;; `rr-abs-triangle', which a `fact' has by then landed and which also mentions
;; `abs' -- the look-alike trap.  Taken before anything else is cited, the only
;; universal in the context IS the hypothesis.
(bl-peel-to! '<=)
(define bl-ag
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "block: no agreement hypothesis"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL) (dk-contains? (car l) 'abs)
                (not (dk-contains? (car l) 'SERIES-PARTIAL-SUM))) (car l))
          (else (loop (cdr l))))))
(have! (list 'AND '(IN m NN) (list 'IN bl-d 'NN)))
(fact 'nn-add-closed 'm bl-d)
(define bl-md (list '+ 'm bl-d))
(mac 'nn-add-succ)
;; both recurrences are guarded on their arguments
(fact 'series-partial-sum-in-rr bl-md 'f)
(fact 'fun-apply-type-c 'f 'NN 'RR bl-md)
(fact 'series-partial-sum-in-rr bl-md 'g)
(fact 'fun-apply-type-c 'g 'NN 'RR bl-md)
(fact 'series-partial-sum-in-rr 'm 'f)
(fact 'series-partial-sum-in-rr 'm 'g)
(mac 'series-partial-sum-succ)
;; regroup so the triangle inequality applies to the two summands
(define bl-Sfmd (list 'SERIES-PARTIAL-SUM 'f bl-md))
(define bl-Sfm  '(SERIES-PARTIAL-SUM f m))
(define bl-Sgmd (list 'SERIES-PARTIAL-SUM 'g bl-md))
(define bl-Sgm  '(SERIES-PARTIAL-SUM g m))
(define bl-fk   (list 'f bl-md))
(define bl-gk   (list 'g bl-md))
(define bl-diff (list '- bl-Sfmd bl-Sfm))
(have! (list '= (list '- (list '+ bl-Sfmd bl-fk) bl-Sfm)
             (list '+ bl-diff bl-fk))
  (lambda () (crs)))
(subst (list '= (list '- (list '+ bl-Sfmd bl-fk) bl-Sfm)
             (list '+ bl-diff bl-fk)))
(fact 'rr-sub-in-rr bl-Sfmd bl-Sfm)
(have! (list 'AND (list 'IN bl-diff 'RR) (list 'IN bl-fk 'RR)))
(fact 'rr-abs-triangle bl-diff bl-fk)
(dk-deepest (lambda ()
  (inst+ (dk-deepest (lambda ()
    (inst+ (dk-deepest (lambda () (inst+ bl-ih 'm))) 'f))) 'g)))
(inst+ bl-ag bl-md)
(fact 'rr-abs-closed bl-diff)
(fact 'rr-abs-closed bl-fk)
(fact 'rr-add-closed bl-diff bl-fk)
(fact 'rr-abs-closed (list '+ bl-diff bl-fk))
(bl-ineq (list '<= (list 'abs (list '+ bl-diff bl-fk))
               (list '+ (list 'abs bl-diff) (list 'abs bl-fk)))
         (list '<= (list 'abs bl-diff) (list '- bl-Sgmd bl-Sgm))
         (list '= bl-gk (list 'abs bl-fk)))
(qed 'series-abs-triangle-block)


;;; m <= k  =>  k = m + d for some d in NN.  Induction on k.
(define (ng-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "ng-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL m (IMPLIES (IN m NN) (IMPLIES (<= m k)
     (FORSOME d (AND (IN d NN) (= k (+ m d)))))))))))
(define ng-br (use-induction))

;;; BASE k = 0:  m <= 0 forces m = 0, and 0 = 0 + 0.
(dk-focus! (cdr (assq 'base ng-br)))
(ng-peel-to! 'FORSOME)
(fact 'nn-le-zero-is-zero 'm)
(fact 'nn-zero-in)
(ew 0)
(mac 'nn-add-zero)            ; m + 0 = m, so the claim is 0 = m
(for-each (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (begin (fact 'eq-sym 'm 0) (ass))))
          (dk-opened (lambda () (di))))

;;; STEP
(dk-focus! (cdr (assq 'step ng-br)))
(define ng-k  (cdr (assq 'var ng-br)))
(define ng-ih (cdr (assq 'ih  ng-br)))
(ng-peel-to! 'FORSOME)
(fact 'nn-le-succ-cases ng-k 'm)          ; m <= k  or  m = succ k
(use-cases
 (list (list '<= 'm ng-k) (list '= 'm (list 'succ ng-k)))
 ;; CASE 1: the induction hypothesis supplies the gap, and one more succ does it.
 (lambda ()
   (let* ((ex (dk-deepest (lambda () (inst+ ng-ih 'm))))
          (dd (let* ((fv0 (apply append (map free-vars (dk-asms))))
                     (landed (dk-landed (lambda () (ai ex)))))
                (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f)))
                          landed)
                (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                                     (apply append (map free-vars (dk-asms))))))
                  (if (null? fresh) (error "gap: no witness appeared") (car fresh))))))
     (fact 'nn-succ-closed dd)
     (ew (list 'succ dd))
     (for-each (lambda (l)
                 (dk-focus! l)
                 (if (eq? (car (dk-goal)) 'IN)
                     (ass)
                     (begin
                       (have! (list 'AND '(IN m NN) (list 'IN dd 'NN)))
                       (mac 'nn-add-succ)
                       ;; goal is succ(k) = succ(m + d); the IH witness says
                       ;; k = m + d, so rewrite and reflect.
                       ;; `rfl' carries a DEFINEDNESS guard (pi-reflexivity!,
                       ;; primitive-inferences.scm:647): t = t needs t defined,
                       ;; syntactically or by a context (IN t _).  succ(m+d) is
                       ;; neither until this typing lands -- and the warning it
                       ;; gives without it says "goal is not (= a a)", which
                       ;; names the wrong reason entirely.
                       (fact 'nn-add-closed 'm dd)
                       (fact 'nn-succ-closed (list '+ 'm dd))
                       (subst (list '= ng-k (list '+ 'm dd)))
                       ;; `qrfl', not `rfl': succ(m + d) is not MANIFESTLY
                       ;; defined, and rfl demands that.
                       (rfl))))
               (dk-opened (lambda () (di))))))
 ;; CASE 2: m IS succ k, so the gap is 0.
 (lambda ()
   (fact 'nn-zero-in)
   (ew 0)
   (mac 'nn-add-zero)
   (for-each (lambda (l)
               (dk-focus! l)
               (if (eq? (car (dk-goal)) 'IN)
                   (ass)
                   (begin (fact 'eq-sym 'm (list 'succ ng-k)) (ass))))
             (dk-opened (lambda () (di))))))
(qed 'nn-le-gap)


;;; ... and the block inequality in the form a Cauchy argument can use.
(sp (make-wff
     '(FORALL k (IMPLIES (IN k NN)
        (FORALL m (IMPLIES (IN m NN)
          (FORALL f (IMPLIES (IN f (FUN NN RR))
            (FORALL g (IMPLIES (IN g (FUN NN RR))
              (IMPLIES (FORALL j (IMPLIES (IN j NN) (= (g j) (abs (f j)))))
                (IMPLIES (<= m k)
                  (<= (abs (- (SERIES-PARTIAL-SUM f k) (SERIES-PARTIAL-SUM f m)))
                      (- (SERIES-PARTIAL-SUM g k) (SERIES-PARTIAL-SUM g m)))))))))))))))
(ng-peel-to! '<=)
(define nb-ag
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "no agreement"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL) (dk-contains? (car l) 'abs)) (car l))
          (else (loop (cdr l))))))
(define nb-ex (dk-deepest (lambda () (fact 'nn-le-gap 'k 'm))))
(define nb-d
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai nb-ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "no gap witness") (car fresh)))))
(subst (list '= 'k (list '+ 'm nb-d)))
(fact 'series-abs-triangle-block nb-d 'm 'f 'g)
(ass)
(qed 'series-abs-triangle-le)


(topic! 'series-abs-triangle-block 'analysis)
(alias! 'series-abs-triangle-block "the block triangle inequality, over a gap")
(topic! 'nn-le-gap 'inequalities)
(alias! 'nn-le-gap "a natural at most another is that other minus a natural")
(topic! 'series-abs-triangle-le 'analysis)
(alias! 'series-abs-triangle-le
        "the absolute value of a block of a series is at most the block of absolute values")
