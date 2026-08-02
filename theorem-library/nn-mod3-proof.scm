;;; nn-mod3-proof.scm -- mod-3 arithmetic on NN, the mirror of nn-parity-proof.scm.
;;;
;;; Everything PROVEN, from the Peano recursion equations, by induction:
;;;   nn-plus-three      x + 3 = succ(succ(succ x))
;;;   nn-three-mul-succ  3 * succ(k) = succ(succ(succ(3k)))
;;;   nn-trichotomy-3    n = 3k  or  succ(3k)  or  succ(succ(3k))     (3-way induction)
;;;   nn-3-not-succ      3x /= succ(3y)     (a multiple of 3 is never == 1 mod 3)
;;;   nn-3-div-square    3 | p*p => 3 | p   (the linchpin of sqrt(3) irrationality)
;;;   nn-3-cancel        3x = 3y => x = y   (instance of nn-mul-cancel)
;;;   nn-lt-triple       k /= 0 => k < 3k   (calc chain, like nn-lt-double)
;;;
;;; Loads after nn-parity-proof (nn-zero-or-succ, nn-succ-inj/nonzero) and nn-integral
;;; (nn-mul-cancel).  The n3- kit is local, copied from nn-parity-proof's np- kit.

;;; --- local kit (n3- prefix), copied from nn-parity-proof.scm's np- kit ---
(define (n3-leaves)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (n3-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (n3-goalof s) (wff-formula (sequent-node-assertion s)))
(define (n3-goal) (n3-goalof (proof-state-focus *ps*)))
(define (n3-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (n3-foc! pred)
  (let ((l (n3-any (lambda (s) (pred (n3-goalof s))) (n3-leaves))))
    (if (not l) (error "n3-foc!: no open leaf matches") (begin (dk-focus! l) l))))
(define (n3-from-context!)
  (let ((g (n3-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (n3-from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g))) (arith))
      (else (ass)))))
(define (n3-cut! form #!optional thunk)
  (let* ((new  (dk-opened (lambda () (cut form))))
         (side (or (n3-any (lambda (s) (alpha-equiv? (n3-goalof s) form)) new)
                   (error "n3-cut!: no side goal for" form)))
         (main (or (n3-any (lambda (s) (not (eq? s side))) new)
                   (error "n3-cut!: no main branch for" form))))
    (dk-focus! side)
    (if (default-object? thunk) (n3-from-context!) (thunk))
    (dk-focus! main) main))
(define (n3-binder-is? v)
  (lambda (s) (let ((g (n3-goalof s)))
                (and (pair? g) (eq? (car g) 'FORALL) (eq? (quantifier-var g) v)))))
(define (n3-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** n3: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (n3-goalof l))) (newline)
                    (for-each (lambda (w) (display "      | ") (display (expression->string (wff-formula w))) (newline))
                              (list-head (sequent-node-assumptions l) (min 6 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "n3: unfinished" name))))

;;; =======================================================================
;;; 3 = succ(succ(succ 0)) ; and  x + 3 = succ(succ(succ x)).   Mirror nn-plus-two.
(sp (make-wff '(= 3 (succ (succ (succ 0))))))
(arith)
(n3-qed! 'nn-three-is-succ3-zero)

(sp (make-wff '(FORALL x (IMPLIES (IN x NN) (= (+ x 3) (succ (succ (succ x))))))))
(di)(di)
(mac 'nn-three-is-succ3-zero)             ; goal: x + succ(succ(succ 0)) = succ(succ(succ x))
(fact 'nn-add-succ 'x '(succ (succ 0)))
(fact 'nn-add-succ 'x '(succ 0))
(fact 'nn-add-succ 'x 0)
(fact 'nn-add-zero 'x)
(subst '(= (+ x (succ (succ (succ 0)))) (succ (+ x (succ (succ 0))))))
(subst '(= (+ x (succ (succ 0))) (succ (+ x (succ 0)))))
(subst '(= (+ x (succ 0)) (succ (+ x 0))))
(subst '(= (+ x 0) x))
(fact 'nn-succ-closed 'x)
(fact 'nn-succ-closed '(succ x))
(fact 'nn-succ-closed '(succ (succ x)))
(rfl)
(n3-qed! 'nn-plus-three)

;;; =======================================================================
;;; 3 * succ(k) = succ(succ(succ(3*k))).   Mirror nn-two-mul-succ.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
                 (= (* 3 (succ k)) (succ (succ (succ (* 3 k)))))))))
(di)(di)
(fact 'nn-mul-succ 3 'k)                  ; 3 * succ k = 3*k + 3   (guard IN 3 NN ground)
(n3-cut! '(AND (IN 3 NN) (IN k NN)) (lambda () (n3-from-context!)))
(fact 'nn-mul-closed 3 'k)                ; IN (* 3 k) NN
(fact 'nn-plus-three '(* 3 k))            ; (3k) + 3 = succ(succ(succ(3k)))
(subst '(= (* 3 (succ k)) (+ (* 3 k) 3)))
(ass)
(n3-qed! 'nn-three-mul-succ)

;;; =======================================================================
;;; TRICHOTOMY:  every natural is 3k, succ(3k), or succ(succ(3k)).  Mirror nn-parity.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
                 (FORSOME k (AND (IN k NN)
                    (OR (= n (* 3 k))
                        (OR (= n (succ (* 3 k)))
                            (= n (succ (succ (* 3 k)))))))))) ))
;; via `use-induction' (driver-kit): runs ni, labels base/step by the binder, and
;; peels the step (introduces n, lands IN n NN and the IH).
(define t3-IND  (use-induction))
(define t3-base (cdr (assq 'base t3-IND)))
(define t3-ih   (cdr (assq 'ih   t3-IND)))

;; base: 0 = 3*0.
(dk-focus! t3-base)
(ew 0)
(for-each (lambda (k) (dk-focus! k)
            (if (eq? (car (n3-goal)) 'OR) (begin (oi-l) (arith)) (arith)))
          (dk-opened (lambda () (di))))

;; step (use-induction already introduced n, IN n NN, and landed the IH).
(dk-focus! (cdr (assq 'step t3-IND)))
(ai t3-ih)
(define t3-conj (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                              (eq? (car (caddr f)) 'OR))) (n3-asms))
                    (error "trich: skolemized IH did not land")))
(ai t3-conj)
(define t3-or (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (n3-asms))
                  (error "trich: no disjunction")))
(define t3-w (caddr (caddr (cadr t3-or))))  ; the w in (= n (* 3 w))

;; typings for rfl definedness across the cases.
(n3-cut! (list 'AND '(IN 3 NN) (list 'IN t3-w 'NN)) (lambda () (n3-from-context!)))
(fact 'nn-mul-closed 3 t3-w)                       ; IN (* 3 w) NN
(fact 'nn-succ-closed (list '* 3 t3-w))            ; IN succ(3w) NN
(fact 'nn-succ-closed (list 'succ (list '* 3 t3-w))) ; IN succ(succ(3w)) NN

;; split the outer OR: [n = 3w]  vs  [inner OR].
(define t3-c1 (dk-opened (lambda () (ai t3-or))))
(define t3-cA (or (n3-any (lambda (s) (n3-any (lambda (w_) (equal? (wff-formula w_) (list '= 'n (list '* 3 t3-w))))
                                              (sequent-node-assumptions s))) t3-c1)
                  (error "trich: no n=3w case")))
(define t3-cB (or (n3-any (lambda (s) (not (eq? s t3-cA))) t3-c1) (error "trich: no inner-OR case")))

;; case A: n = 3w -> succ n = succ(3w)  (2nd disjunct, witness w).
(dk-focus! t3-cA)
(ew t3-w)
(for-each (lambda (leaf) (dk-focus! leaf)
            (if (eq? (car (n3-goal)) 'IN) (ass)
                (begin (oi-r) (oi-l) (subst (list '= 'n (list '* 3 t3-w))) (rfl))))
          (dk-opened (lambda () (di))))

;; case B: inner OR -- split [n = succ(3w)] vs [n = succ(succ(3w))].
(dk-focus! t3-cB)
(define t3-innor (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (n3-asms))
                     (error "trich: no inner OR in context")))
(define t3-c2 (dk-opened (lambda () (ai t3-innor))))
(define t3-cB1 (or (n3-any (lambda (s) (n3-any (lambda (w_) (equal? (wff-formula w_) (list '= 'n (list 'succ (list '* 3 t3-w)))))
                                               (sequent-node-assumptions s))) t3-c2)
                   (error "trich: no n=succ(3w) case")))
(define t3-cB2 (or (n3-any (lambda (s) (not (eq? s t3-cB1))) t3-c2) (error "trich: no n=succ(succ(3w)) case")))

;; case B1: n = succ(3w) -> succ n = succ(succ(3w))  (3rd disjunct, witness w).
(dk-focus! t3-cB1)
(ew t3-w)
(for-each (lambda (leaf) (dk-focus! leaf)
            (if (eq? (car (n3-goal)) 'IN) (ass)
                (begin (oi-r) (oi-r) (subst (list '= 'n (list 'succ (list '* 3 t3-w)))) (rfl))))
          (dk-opened (lambda () (di))))

;; case B2: n = succ(succ(3w)) -> succ n = succ(succ(succ(3w))) = 3*succ(w)  (1st disjunct, witness succ w).
(dk-focus! t3-cB2)
(fact 'nn-succ-closed t3-w)
(fact 'nn-three-mul-succ t3-w)              ; 3*succ w = succ(succ(succ(3w)))
(ew (list 'succ t3-w))
(for-each (lambda (leaf) (dk-focus! leaf)
            (if (eq? (car (n3-goal)) 'IN) (n3-from-context!)
                (begin (oi-l)
                       (subst (list '= 'n (list 'succ (list 'succ (list '* 3 t3-w)))))  ; succ n -> succ(succ(succ(3w)))
                       (subst (list '= (list '* 3 (list 'succ t3-w))
                                    (list 'succ (list 'succ (list 'succ (list '* 3 t3-w))))))  ; 3*succ w -> that
                       (rfl))))
          (dk-opened (lambda () (di))))
(n3-qed! 'nn-trichotomy-3)

;;; =======================================================================
;;; EXCLUSIVITY:  3x is never succ(3y).  (A multiple of 3 is never == 1 mod 3.)
;;; Mirror nn-parity-exclusive, one succ-layer deeper.
(sp (make-wff '(FORALL x (IMPLIES (IN x NN)
                 (FORALL y (IMPLIES (IN y NN)
                   (NOT (= (* 3 x) (succ (* 3 y))))))))))
(define e3-branches (dk-opened (lambda () (ni))))
(define e3-step (or (n3-any (n3-binder-is? 'x) e3-branches) (error "excl: no step")))
(define e3-base (or (n3-any (lambda (s) (not (eq? s e3-step))) e3-branches) (error "excl: no base")))

;; base: 3*0 = 0, and 0 is not a successor.
(dk-focus! e3-base)
(di)(di)(di)                               ; y ; IN y NN ; assume 3*0 = succ(3y) ; FALSITY
(n3-cut! '(AND (IN 3 NN) (IN y NN)))
(fact 'nn-mul-closed 3 'y)                 ; IN (* 3 y) NN
(n3-cut! '(= (* 3 0) 0) (lambda () (arith)))
(n3-cut! '(= 0 (succ (* 3 y)))
         (lambda () (subst '(= 0 (* 3 0))) (ass)))
(fact 'nn-succ-nonzero '(* 3 y))
(fact 'neq-sym '(succ (* 3 y)) 0)
(ai '(NOT (= 0 (succ (* 3 y)))))

;; step.
(dk-focus! e3-step)
(di)                                       ; x ; IN x NN
(define e3-ih (dk-landed-1 (lambda () (di))))          ; IH: forall y. 3x /= succ(3y)
(di)                                       ; y ; IN y NN
(di)                                       ; assume 3*succ x = succ(3y) ; FALSITY
(n3-cut! '(AND (IN 3 NN) (IN x NN)))
(fact 'nn-mul-closed 3 'x)
(fact 'nn-succ-closed '(* 3 x))
(fact 'nn-succ-closed '(succ (* 3 x)))
(fact 'nn-three-mul-succ 'x)               ; 3*succ x = succ(succ(succ(3x)))
(fact 'nn-zero-or-succ 'y)
(define e3-or (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (n3-asms))
                  (error "excl: no y-split")))
(define e3-cases (dk-opened (lambda () (ai e3-or))))
(define e3-zero (or (n3-any (lambda (s) (n3-any (lambda (w) (equal? (wff-formula w) '(= y 0)))
                                                (sequent-node-assumptions s))) e3-cases)
                    (error "excl: no y=0")))
(define e3-succ (or (n3-any (lambda (s) (not (eq? s e3-zero))) e3-cases) (error "excl: no y=succ")))

;; y = 0: succ(succ(succ 3x)) = succ(3*0), strip one succ, succ(succ 3x) = 0, absurd.
(dk-focus! e3-zero)
(n3-cut! '(= (succ (succ (succ (* 3 x)))) (succ (* 3 0)))
         (lambda () (subst '(= (succ (succ (succ (* 3 x)))) (* 3 (succ x))))
                    (subst '(= 0 y)) (ass)))
(fact 'nn-mul-closed 3 0)
(fact 'nn-succ-inj '(succ (succ (* 3 x))) '(* 3 0))    ; succ(succ 3x) = 3*0
(n3-cut! '(= (* 3 0) 0) (lambda () (arith)))
(n3-cut! '(= (succ (succ (* 3 x))) 0) (lambda () (subst '(= 0 (* 3 0))) (ass)))
(fact 'nn-succ-nonzero '(succ (* 3 x)))
(ai '(NOT (= (succ (succ (* 3 x))) 0)))

;; y = succ(q): succ^3(3x) = succ^4(3q), strip three succs -> 3x = succ(3q), IH forbids.
(dk-focus! e3-succ)
(define e3-ex (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (n3-asms))
                  (error "excl: no existential in y=succ")))
(define e3-conj (dk-landed-1 (lambda () (ai e3-ex))))   ; (IN q NN) and y = succ q
(ai e3-conj)
(define e3-q (cadr (caddr (caddr e3-conj))))            ; the q in y = succ q
(n3-cut! (list 'AND '(IN 3 NN) (list 'IN e3-q 'NN)))
(fact 'nn-mul-closed 3 e3-q)
(fact 'nn-succ-closed (list '* 3 e3-q))
(fact 'nn-succ-closed (list 'succ (list '* 3 e3-q)))
(fact 'nn-succ-closed (list 'succ (list 'succ (list '* 3 e3-q))))
(fact 'nn-three-mul-succ e3-q)             ; 3*succ q = succ(succ(succ(3q)))
(n3-cut! (list '= '(succ (succ (succ (* 3 x))))
               (list 'succ (list 'succ (list 'succ (list 'succ (list '* 3 e3-q))))))
         (lambda ()
           (subst '(= (succ (succ (succ (* 3 x)))) (* 3 (succ x))))                 ; LHS -> 3*succ x
           (subst (list '= (list 'succ (list 'succ (list 'succ (list '* 3 e3-q))))
                        (list '* 3 (list 'succ e3-q))))                              ; succ^3(3q) -> 3*succ q
           (subst (list '= (list 'succ e3-q) 'y))                                   ; succ q -> y
           (ass)))
(fact 'nn-succ-inj '(succ (succ (* 3 x))) (list 'succ (list 'succ (list 'succ (list '* 3 e3-q)))))
(fact 'nn-succ-inj '(succ (* 3 x)) (list 'succ (list 'succ (list '* 3 e3-q))))
(fact 'nn-succ-inj '(* 3 x) (list 'succ (list '* 3 e3-q)))   ; 3x = succ(3q)
(inst+ e3-ih e3-q)                         ; IH at q: NOT(3x = succ(3q))
(ai (list 'NOT (list '= '(* 3 x) (list 'succ (list '* 3 e3-q)))))
(n3-qed! 'nn-3-not-succ)

;;; =======================================================================
;;; nn-3-div-square : 3 | p*p => 3 | p.   Mirror nn-even-square, three residues.
(sp (make-wff '(FORALL p (IMPLIES (IN p NN)
                 (IMPLIES (FORSOME m (AND (IN m NN) (= (* p p) (* 3 m))))
                          (FORSOME k (AND (IN k NN) (= p (* 3 k)))))))))
(di)(di)(di)                               ; p ; IN p NN ; assume (forsome m. p*p = 3m)
(define ds-mex (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (n3-asms))
                   (error "divsq: no m")))
(ai ds-mex)
(define ds-mc (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                            (eq? (car (caddr f)) '=))) (n3-asms)) (error "divsq: no m body")))
(ai ds-mc)
(define ds-meq (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (cadr f) '(* p p)))) (n3-asms))
                   (error "divsq: no p*p=3m")))
(define ds-m (caddr (caddr ds-meq)))       ; p*p = 3*m
(fact 'nn-trichotomy-3 'p)
(define ds-tri (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (n3-asms))
                   (error "divsq: trichotomy did not land")))
(ai ds-tri)
(define ds-tc (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                            (eq? (car (caddr f)) 'OR))) (n3-asms)) (error "divsq: no trich body")))
(ai ds-tc)
(define ds-or (or (n3-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (n3-asms)) (error "divsq: no residue split")))
(define ds-w (caddr (caddr (cadr ds-or)))) ; w in (= p (* 3 w))
;; typings for w
(n3-cut! (list 'AND '(IN 3 NN) (list 'IN ds-w 'NN)) (lambda () (n3-from-context!)))
(fact 'nn-mul-closed 3 ds-w)               ; IN (* 3 w) NN
(fact 'nn-succ-closed (list '* 3 ds-w))
(fact 'nn-succ-closed (list 'succ (list '* 3 ds-w)))

;; helper: contradiction at a nonzero residue.  Caller has established (IN J NN);
;; PEQ is p = <residue form>; CONVERT-THUNK rewrites the residue's succ-form to +form.
(define (ds-contra! peq jj convert-thunk)
  (pbc)                                                                     ; goal FALSITY
  (n3-cut! (list 'AND '(IN 3 NN) (list 'IN jj 'NN)) (lambda () (n3-from-context!)))
  (fact 'nn-mul-closed 3 jj)                                                ; 3J in NN
  (fact 'nn-3-not-succ ds-m jj)                                             ; NOT(3m = succ(3J))
  (n3-cut! (list '= (list '* 3 ds-m) (list 'succ (list '* 3 jj)))
           (lambda ()
             (subst (list '= (list '* 3 ds-m) '(* p p)))                    ; 3m -> p*p
             (subst peq)                                                    ; p -> residue form
             (convert-thunk)                                               ; succ-forms -> +1 / +2
             (fact 'nn-succ-plus-one (list '* 3 jj))                        ; succ(3J) = 3J+1
             (subst (list '= (list 'succ (list '* 3 jj)) (list '+ (list '* 3 jj) 1)))
             (crs)))
  (ai (list 'NOT (list '= (list '* 3 ds-m) (list 'succ (list '* 3 jj))))))

;; w*w and 3*w*w are shared by both nonzero cases -- establish once, up front.
(n3-cut! (list 'AND (list 'IN ds-w 'NN) (list 'IN ds-w 'NN)) (lambda () (n3-from-context!)))
(fact 'nn-mul-closed ds-w ds-w)                                            ; w*w in NN
(n3-cut! (list 'AND '(IN 3 NN) (list 'IN (list '* ds-w ds-w) 'NN)) (lambda () (n3-from-context!)))
(fact 'nn-mul-closed 3 (list '* ds-w ds-w))                               ; 3*w*w in NN

;; three cases from (OR (=p 3w) (OR (=p succ3w) (=p succ^2 3w))) -- now via
;; `use-cases' (driver-kit): it opens + FLATTENS the nested OR and labels each
;; branch by the residue equality it landed, so we dispatch on the marker rather
;; than re-finding branches by landed-equality by hand.
(for-each-case (use-cases ds-or)
  (lambda (marker)
    (cond
      ;; case A: p = 3w -- witness w.
      ((equal? marker (list '= 'p (list '* 3 ds-w)))
       (ew ds-w)
       (for-each (lambda (leaf) (dk-focus! leaf)
                   (if (eq? (car (n3-goal)) 'IN) (n3-from-context!) (ass)))
                 (dk-opened (lambda () (di)))))
      ;; case B1: p = succ(3w) = 3w+1.  J = 3*w*w + 2*w.
      ((equal? marker (list '= 'p (list 'succ (list '* 3 ds-w))))
       (n3-cut! (list 'AND '(IN 2 NN) (list 'IN ds-w 'NN)) (lambda () (n3-from-context!)))
       (fact 'nn-mul-closed 2 ds-w)                                              ; 2*w in NN
       (n3-cut! (list 'AND (list 'IN (list '* 3 (list '* ds-w ds-w)) 'NN) (list 'IN (list '* 2 ds-w) 'NN))
                (lambda () (n3-from-context!)))
       (fact 'nn-add-closed (list '* 3 (list '* ds-w ds-w)) (list '* 2 ds-w))    ; J = 3ww+2w in NN
       (ds-contra!
         (list '= 'p (list 'succ (list '* 3 ds-w)))
         (list '+ (list '* 3 (list '* ds-w ds-w)) (list '* 2 ds-w))
         (lambda ()
           (fact 'nn-succ-plus-one (list '* 3 ds-w))                             ; succ(3w) = 3w+1
           (subst (list '= (list 'succ (list '* 3 ds-w)) (list '+ (list '* 3 ds-w) 1))))))
      ;; case B2: p = succ(succ(3w)) = 3w+2.  J = 3*w*w + 4*w + 1.
      (else
       (n3-cut! (list 'AND '(IN 4 NN) (list 'IN ds-w 'NN)) (lambda () (n3-from-context!)))
       (fact 'nn-mul-closed 4 ds-w)                                             ; 4*w in NN
       (n3-cut! (list 'AND (list 'IN (list '* 4 ds-w) 'NN) '(IN 1 NN)) (lambda () (n3-from-context!)))
       (fact 'nn-add-closed (list '* 4 ds-w) 1)                                 ; 4w+1 in NN
       (n3-cut! (list 'AND (list 'IN (list '* 3 (list '* ds-w ds-w)) 'NN) (list 'IN (list '+ (list '* 4 ds-w) 1) 'NN))
                (lambda () (n3-from-context!)))
       (fact 'nn-add-closed (list '* 3 (list '* ds-w ds-w)) (list '+ (list '* 4 ds-w) 1))  ; J in NN
       (ds-contra!
         (list '= 'p (list 'succ (list 'succ (list '* 3 ds-w))))
         (list '+ (list '* 3 (list '* ds-w ds-w)) (list '+ (list '* 4 ds-w) 1))
         (lambda ()
           (fact 'nn-plus-two (list '* 3 ds-w))                                  ; 3w+2 = succ(succ(3w))
           (subst (list '= (list 'succ (list 'succ (list '* 3 ds-w))) (list '+ (list '* 3 ds-w) 2)))))))))
(n3-qed! 'nn-3-div-square)

;;; =======================================================================
;;; nn-3-cancel : 3x = 3y => x = y.  Instance of nn-mul-cancel (commute to x*3).
(sp (make-wff '(FORALL x (IMPLIES (IN x NN) (FORALL y (IMPLIES (IN y NN)
                 (IMPLIES (= (* 3 x) (* 3 y)) (= x y))))))))
(di)(di)(di)(di)(di)
(n3-cut! '(= (* x 3) (* 3 x)) (lambda () (crs)))
(n3-cut! '(= (* y 3) (* 3 y)) (lambda () (crs)))
(n3-cut! '(= (* x 3) (* y 3))
         (lambda () (subst '(= (* x 3) (* 3 x))) (subst '(= (* y 3) (* 3 y))) (ass)))
(fact 'nn-mul-cancel 'x 'y 3)
(ass)
(n3-qed! 'nn-3-cancel)

;;; nn-lt-triple : k /= 0 => k < 3*k.  `calc' chain  k = k+0 < k+k+k = 3k.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< k (* 3 k)))))))
(di)(di)(di)
(fact 'nn-pos-of-nonzero 'k)
(calc 'k '(= (+ k 0)) '(< (+ (+ k k) k)) '(= (* 3 k)))
(n3-qed! 'nn-lt-triple)
