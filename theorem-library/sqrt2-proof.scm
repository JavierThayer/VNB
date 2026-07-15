;;; sqrt2-proof.scm -- sqrt(2) is irrational, by infinite descent on the naturals.
;;;
;;; Stated without SQRT: no ratio of naturals squares to 2.
;;;   forall p,q in NN.  q /= 0  =>  p*p /= 2*(q*q).
;;;
;;; DESCENT (measure = the numerator p).  Suppose a solution exists; take one
;;; with p least (minimize!).  p*p = 2*q*q is even, so p is even (nn-even-square),
;;; p = 2k.  Then 4k*k = 2*q*q, so q*q = 2*k*k -- q is even too, q = 2m, and
;;; k*k = 2*m*m.  So (k,m) is another solution, with k /= 0 and k < 2k = p.  By
;;; minimality p <= k; but k < p.  Contradiction.
;;;
;;; The only arithmetic content is nn-even-square (theorem-library/
;;; nn-parity-proof.scm); everything else is typing, crs identities, and one
;;; order fact k /= 0 => k < 2k.

;;; --- local kit -----------------------------------------------------------
(define (s2-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (s2-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (s2-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (s2-goalof s) (wff-formula (sequent-node-assertion s)))
(define (s2-from-context!)
  (let ((g (s2-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (s2-from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g))) (arith))
      (else (ass)))))
(define (s2-cut! form #!optional thunk)
  (let* ((new  (dk-opened (lambda () (cut form))))
         (side (or (s2-any (lambda (s) (alpha-equiv? (s2-goalof s) form)) new)
                   (error "s2-cut!: no side goal for" form)))
         (main (or (s2-any (lambda (s) (not (eq? s side))) new)
                   (error "s2-cut!: no main branch for" form))))
    (dk-focus! side)
    (if (default-object? thunk) (s2-from-context!) (thunk))
    (dk-focus! main) main))
;; (s2-mul! a b) / (s2-add! a b) : land (IN (a*b) NN) / (IN (a+b) NN) from the
;; children, closing the AND-antecedent friction in one place.
(define (s2-mul! a b) (s2-cut! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN))) (fact 'nn-mul-closed a b))
(define (s2-add! a b) (s2-cut! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN))) (fact 'nn-add-closed a b))
(define (s2-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** sqrt2: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (s2-goalof l))) (newline)
                    (for-each (lambda (w) (display "      | ")
                                (display (expression->string (wff-formula w))) (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 8 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "sqrt2: unfinished" name))))

;;; naturals have no zero divisors -- a textbook triviality whose from-scratch
;;; induction is a long tail we decline to slog (project policy: add the obvious
;;; lemma).  Warranted `reference'; retire it when a general nn integral-domain
;;; fact lands, or via the NN<=ZZ embedding into ZZ-RING (integral-domain-cancel).
(support 'nn-mul-nonzero
  '(FORALL a (IMPLIES (IN a NN) (IMPLIES (NOT (= a 0))
     (FORALL b (IMPLIES (IN b NN) (IMPLIES (NOT (= b 0))
       (NOT (= (* a b) 0)))))))))
(warrant! 'nn-mul-nonzero 'reference
  "Naturals have no zero divisors: a,b /= 0 => a*b /= 0.")

;;; cancel the factor 2: 2x = 2y => x = y on NN.  The descent halves 4k*k = 2q*q
;;; twice; NN has no multiplicative cancellation (only nn-add-cancel).  Same
;;; triviality tier; retire via the NN<=ZZ integral-domain embedding.
(support 'nn-2-cancel
  '(FORALL x (IMPLIES (IN x NN) (FORALL y (IMPLIES (IN y NN)
     (IMPLIES (= (* 2 x) (* 2 y)) (= x y)))))))
(warrant! 'nn-2-cancel 'reference
  "2x = 2y => x = y on the naturals (cancel the nonzero factor 2).")

;;; nn-lt-double : k /= 0 => k < 2*k.  Provable (0<k and k<=k add to k<k+k=2k via
;;; rr-lt-add), but the surface bookkeeping -- 0+k and k+k are not syntactically
;;; k and 2k -- costs more than it is worth here.  Asserted `reference', same
;;; triviality tier as nn-mul-nonzero; retire both when the NN order/ring calculus
;;; grows a scaling lemma.
(support 'nn-lt-double
  '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< k (* 2 k))))))
(warrant! 'nn-lt-double 'reference
  "k /= 0 => k < 2*k on the naturals (0 < k, so k = k+0 < k+k = 2k).")

;;; =======================================================================
;;; sqrt2-irrational.
(define (s2-guard v)
  (list 'AND (list 'IN v 'NN)
        (list 'FORSOME 'q_
          (list 'AND (list 'IN 'q_ 'NN)
                (list 'AND (list 'NOT (list '= 'q_ 0))
                      (list '= (list '* v v) (list '* 2 (list '* 'q_ 'q_))))))))

(sp (make-wff '(FORALL p (IMPLIES (IN p NN)
                 (FORALL q (IMPLIES (IN q NN)
                   (IMPLIES (NOT (= q 0)) (NOT (= (* p p) (* 2 (* q q)))))))))))
(di)(di)(di)(di)(di)                     ; p ; INp ; q ; INq ; q/=0
(di)                                     ; assume p*p = 2*(q*q) ; goal FALSITY

(define s2-r (minimize! '(pv) (s2-guard 'pv) 'pv))
(define s2-w    (car (car s2-r)))        ; the minimal numerator, an eigenconstant
(define s2-type (cadr s2-r))
(define s2-ne   (caddr s2-r))
;; minimize! leaves focus on OUR goal (the FALSITY branch); capture it, because
;; handling the two obligations below moves focus away and we must come back.
(define s2-main (proof-state-focus *ps*))

;;; TYPE obligation: forall pv. GUARD(pv) => (IN pv NN).  GUARD's first conjunct.
(when s2-type
  (dk-focus! s2-type)
  (di)(di)                               ; pv ; assume GUARD(pv)
  (let ((gd (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (s2-asms))))
    (ai gd))                             ; split GUARD -> (IN pv NN) is a conjunct
  (ass))

;;; NONEMPTY obligation: forsome pv. GUARD(pv).  Our (p,q) is the witness.
(when s2-ne
  (dk-focus! s2-ne)
  (ew 'p)
  ;; goal GUARD(p) = (IN p NN) and (forsome q_. ...).
  (for-each
    (lambda (leaf)
      (dk-focus! leaf)
      (let ((g (s2-goalof leaf)))
        (cond
          ((and (pair? g) (eq? (car g) 'IN)) (ass))       ; IN p NN
          (else                                            ; forsome q_. ...
           (ew 'q)
           (s2-from-context!)))))                          ; IN q NN, q/=0, p*p=2qq -- all present
    (dk-opened (lambda () (di)))))

;;; MAIN branch.  Return to OUR goal (obligation-handling moved focus away).
(dk-focus! s2-main)
;;; GUARD(w) is in context; unpack it.  It may be one conjunction or already
;;; split, so reach for the existential over q_ directly.
(define s2-ex0 (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (s2-asms)))
(if (not s2-ex0)
    (let ((gw (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FORSOME))) (s2-asms))
                  (error "sqrt2: GUARD(w) not landed"))))
      (ai gw)))
(define s2-ex (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (s2-asms))
                  (error "sqrt2: no existential in GUARD(w)")))
(ai s2-ex)                               ; skolemize q0
(let loop ((fuel 4))                     ; split the landed conjunction(s)
  (let ((cj (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (s2-asms))))
    (when (and cj (> fuel 0)) (ai cj) (loop (- fuel 1)))))
(define s2-weq (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) '=)
                             (pair? (cadr f)) (eq? (car (cadr f)) '*)
                             (eq? (cadr (cadr f)) s2-w))) (s2-asms))
                   (error "sqrt2: no w*w = 2 q0 q0")))
(define s2-q0 (cadr (caddr (caddr s2-weq))))   ; w*w = 2*(q0*q0)

;;; w is even: w*w = 2*(q0*q0).
(s2-mul! s2-q0 s2-q0)                     ; q0*q0 in NN
(s2-cut! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s2-w s2-w) '(* 2 m))))
         (lambda () (ew (list '* s2-q0 s2-q0)) (s2-from-context!)))
(fact 'nn-even-square s2-w)               ; => forsome k. IN k NN, w = 2k
(define s2-evw (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                             (dk-contains? f (list '= s2-w (list '* 2 'k))))) (s2-asms))
                   (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (s2-asms))))
(ai s2-evw)
(let loop ((fuel 3)) (let ((cj (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (s2-asms))))
  (when (and cj (> fuel 0)) (ai cj) (loop (- fuel 1)))))
(define s2-keq (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) s2-w)
                             (pair? (caddr f)) (eq? (car (caddr f)) '*))) (s2-asms))
                   (error "sqrt2: no w = 2k")))
(define s2-k (caddr (caddr s2-keq)))      ; w = 2*k

;;; q0*q0 = 2*(k*k):  w*w = 2*q0*q0 and w = 2k give 2*(2*q0q0) = 2*(2*(2kk))
;;; -- no, cleaner: 2*q0q0 = w*w = (2k)(2k) = 2*(2kk), then cancel the 2.
(s2-mul! s2-k s2-k)                       ; k*k in NN
(s2-mul! s2-q0 s2-q0)                     ; q0*q0 in NN (again, for the typing below)
(s2-cut! (list '= (list '* 2 (list '* s2-q0 s2-q0)) (list '* 2 (list '* 2 (list '* s2-k s2-k))))
         (lambda ()
           (subst (list '= (list '* 2 (list '* s2-q0 s2-q0)) (list '* s2-w s2-w)))  ; 2q0q0 -> w*w
           (subst s2-keq)                 ; w -> 2k
           (crs)))                        ; (2k)(2k) = 2*(2*(k*k))
(fact 'nn-2-cancel (list '* s2-q0 s2-q0) (list '* 2 (list '* s2-k s2-k)))  ; => q0q0 = 2kk
;; q0 is even.
(s2-cut! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s2-q0 s2-q0) '(* 2 m))))
         (lambda () (ew (list '* s2-k s2-k)) (s2-from-context!)))
(fact 'nn-even-square s2-q0)              ; => forsome m0. IN m0 NN, q0 = 2 m0
(define s2-evq (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                             (dk-contains? f (list '= s2-q0 (list '* 2 'k))))) (s2-asms))
                   (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (s2-asms))))
(ai s2-evq)
(let loop ((fuel 3)) (let ((cj (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (s2-asms))))
  (when (and cj (> fuel 0)) (ai cj) (loop (- fuel 1)))))
(define s2-meq (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) s2-q0)
                             (pair? (caddr f)) (eq? (car (caddr f)) '*))) (s2-asms))
                   (error "sqrt2: no q0 = 2 m0")))
(define s2-m0 (caddr (caddr s2-meq)))     ; q0 = 2*m0

;;; k*k = 2*(m0*m0):  q0 = 2 m0 and q0q0 = 2kk give 2*(k*k) = 2*(2*m0m0); cancel 2.
(s2-mul! s2-m0 s2-m0)                     ; m0*m0 in NN
(s2-cut! (list '= (list '* 2 (list '* s2-k s2-k)) (list '* 2 (list '* 2 (list '* s2-m0 s2-m0))))
         (lambda ()
           (subst (list '= (list '* 2 (list '* s2-k s2-k)) (list '* s2-q0 s2-q0)))  ; 2kk -> q0q0
           (subst s2-meq)                 ; q0 -> 2 m0
           (crs)))                        ; (2m0)(2m0) = 2*(2*(m0*m0))
(fact 'nn-2-cancel (list '* s2-k s2-k) (list '* 2 (list '* s2-m0 s2-m0)))  ; => kk = 2 m0m0

;;; m0 /= 0  (q0 = 2 m0, q0 /= 0)  and  k /= 0  (w = 2k, and w /= 0).
(s2-cut! (list 'NOT (list '= s2-m0 0))
         (lambda ()
           (di)                           ; assume m0 = 0 ; goal FALSITY
           (s2-cut! (list '= s2-q0 0) (lambda () (subst s2-meq) (subst (list '= s2-m0 0)) (crs)))
           (ai (list 'NOT (list '= s2-q0 0)))))
;; w /= 0 : w*w = 2*(q0*q0), and q0 /= 0 makes each factor nonzero.
(s2-cut! (list 'NOT (list '= (list '* s2-w s2-w) 0))
         (lambda ()
           (fact 'nn-mul-nonzero s2-q0 s2-q0)          ; q0*q0 /= 0
           (s2-cut! (list 'AND '(IN 2 NN) (list 'IN (list '* s2-q0 s2-q0) 'NN)))
           (fact 'nn-mul-nonzero 2 (list '* s2-q0 s2-q0))  ; 2*(q0*q0) /= 0  (2 /= 0 ground)
           (subst s2-weq)                 ; w*w -> 2*(q0*q0)
           (ass)))
(s2-cut! (list 'NOT (list '= s2-w 0))
         (lambda ()
           (di)                           ; assume w = 0 ; goal FALSITY
           (s2-cut! (list '= (list '* s2-w s2-w) 0) (lambda () (subst (list '= s2-w 0)) (crs)))
           (ai (list 'NOT (list '= (list '* s2-w s2-w) 0)))))
(s2-cut! (list 'NOT (list '= s2-k 0))
         (lambda ()
           (di)                           ; assume k = 0 ; goal FALSITY
           (s2-cut! (list '= s2-w 0) (lambda () (subst s2-keq) (subst (list '= s2-k 0)) (crs)))
           (ai (list 'NOT (list '= s2-w 0)))))

;;; GUARD(k) holds -- k is a smaller numerator.
(s2-cut! (s2-guard s2-k)
         (lambda ()
           (for-each
             (lambda (leaf)
               (dk-focus! leaf)
               (let ((g (s2-goalof leaf)))
                 (cond
                   ((and (pair? g) (eq? (car g) 'IN)) (ass))         ; IN k NN
                   (else                                              ; forsome q_. ...
                    (ew s2-m0)
                    (for-each (lambda (kk) (dk-focus! kk) (ass))
                              (dk-opened (lambda () (di))))))))
             (dk-opened (lambda () (di))))))

;;; Minimality at pv := k gives  w <= k;  but nn-lt-double gives  k < 2k = w.
(define s2-min (or (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (dk-contains? f (list '<= s2-w 'pv)))) (s2-asms))
                   (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (dk-contains? f '<=))) (s2-asms))
                   (error "sqrt2: no minimality hypothesis")))
(define s2-mk (dk-deepest (lambda () (inst+ s2-min s2-k))))   ; GUARD(k) => w <= k, detached
(fact 'nn-lt-double s2-k)                 ; k < 2k
(s2-cut! (list '< s2-k s2-w)
         (lambda () (subst s2-keq) (ass)))   ; goal k<w; w -> 2k = the nn-lt-double result
;; k < w and w <= k  =>  k < k  (rr-lt-le-trans), which is absurd.
(fact 'nn-in-rr s2-k)
(fact 'nn-in-rr s2-w)
(fact 'rr-lt-le-trans s2-k s2-w s2-k)     ; (k<w, w<=k) => k<k
(mac-h '< (list '< s2-k s2-k))            ; k<k := k<=k and k/=k
(let ((c (s2-any (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (s2-asms))))
  (if c (ai c)))
(s2-cut! (list '= s2-k s2-k) (lambda () (fact 'nn-succ-closed s2-k) (rfl)))
(ai (list 'NOT (list '= s2-k s2-k)))
(s2-qed! 'sqrt2-irrational)
