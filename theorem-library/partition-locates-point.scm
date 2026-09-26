;;; partition-locates-point.scm -- docs/calculus.pdf Ch 4 Sec 1.
;;;
;;;   p a partition of [a,b] with n pieces,  x in [a,b]
;;;      ==>  exists i < n  with  p(i) <= x <= p(succ i)
;;;
;;; The lemma both remaining halves of Proposition 4.5 need: `step-is-regulated'
;;; (the notes' Remark 4.4, "clearly") and the necessity direction both have to
;;; say WHICH piece a point falls in, and neither can until this is available.
;;;
;;; WHY IS-PARTITION TYPES ITS FAMILY TOTAL ON NN.  This proof is the reason.
;;; The induction step needs the SAME family read as a partition with one piece
;;; fewer.  Typed `p in FUN(INTERVAL(0,n), RR)' that is a DIFFERENT FUNCTION:
;;; you must build the restriction as a VNB-LAMBDA, discharge lam-t's two leaves
;;; (pointwise typing and sethood of the domain), and re-establish all four
;;; conjuncts for the new object.  Typed `p in FUN(NN, RR)' with the conditions
;;; constrained only on 0..n, the step is literally the same `p' with `n'
;;; replaced by its predecessor, and the sub-partition is built by discharging
;;; conjuncts that are already in context -- only monotonicity on the smaller
;;; index range has any content.  The extra domain carries no information; a
;;; finite sequence always extends.
;;;
;;; THREE CASES, and the middle one is easy to miss:
;;;   p(n) < x        -- i := n
;;;   x <= p(n), n=0  -- i := n again, since p(0) = a <= x.  The induction
;;;                      hypothesis is UNAVAILABLE here: a partition with zero
;;;                      pieces is not one (IS-PARTITION demands 1 <= n).
;;;   x <= p(n), 1<=n -- the induction hypothesis, on [a, p(n)]
;;;
;;; The base case n = 0 is vacuous: IS-PARTITION demands `1 <= n'.  Note `prop'
;;; CANNOT close it -- over its atom cap it narrows to the goal-connected
;;; assumptions and the contradiction (0 <= 0 against not(0 <= 0)) is
;;; disconnected from the existential goal, so it is dropped and the panel
;;; reports "does not follow" with a countermodel.  `ai' does the NOT-elim.

(define loc-stmt
  "forall([n], n in nn implies forall([p, a, b, x], is-partition(p, n, a, b) implies x in ccint(a, b) implies forsome([i_], i_ in interval(0, n) and i_ < n and p(i_) <= x and x <= p(succ(i_)))))")
(define (lc-asm pred)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "lc-asm: nothing matches"))
          ((pred (car as)) i)
          (else (loop (cdr as) (+ i 1))))))
(define (lc-focus-head! h)
  (dk-focus! (or (find-first (lambda (nd) (let ((g (wff-formula (sequent-node-assertion nd))))
                                            (and (pair? g) (eq? (car g) h))))
                             (proof-leaves))
                 (error "lc-focus-head!: no open leaf with head" h))))
(sp (make-wff loc-stmt))
(quietly (lambda () (ni)))
;; --- base case ---
(quietly (lambda ()
  (di) (di) (di)
  (mac-h 'is-partition '(IS-PARTITION p 0 a b))
  (dk-split! (car (dk-asms)))
  (fact 'nn-not-le-zero-pos 0)
  (fact 'nn-le-refl 0)
  (ai (lc-asm (lambda (g) (equal? g '(NOT (<= 0 0))))))))
;; --- step: peel into it ---
(quietly (lambda ()
  (dk-focus! (car (proof-leaves)))
  (di) (di) (di) (di)
  (mac-h 'is-partition '(IS-PARTITION p (SUCC n) a b))
  (dk-split! (car (dk-asms)))
  (di)
  (mac-h 'ccint-membership '(IN x (CCINT a b)))
  (dk-split! (let loop ((as (dk-asms)))
               (cond ((null? as) (error "unfolded ccint not found"))
                     ((and (pair? (car as)) (eq? (caar as) 'AND)
                           (equal? (cadr (car as)) '(IN x RR))) (car as))
                     (else (loop (cdr as))))))
  ;; the two partition points we will compare x against
  (fact 'fun-apply-type-c 'p 'NN 'RR 'n)
  (fact 'fun-apply-type-c 'p 'NN 'RR '(SUCC n))))
(quietly (lambda () (use-em (list '<= 'x (list 'p 'n)))))
;; ================= BRANCH B:  p(n) < x,  so  i_ := n  =================
(quietly (lambda ()
  (dk-focus! (find-first (lambda (nd) (equal? (car (dk-asms-of nd)) '(NOT (<= x (p n)))))
                         (proof-leaves)))
  ;; p(n) <= x, from the negation and totality
  (fact 'rr-le-total 'x (list 'p 'n))
  (have! (list '<= (list 'p 'n) 'x) (lambda () (prop)))
  ;; x <= p(succ n), since p(succ n) = b and x <= b
  (have! (list '<= 'x (list 'p (list 'SUCC 'n)))
         (lambda () (subst (list '= (list 'p (list 'SUCC 'n)) 'b)) (ass)))
  ;; n < succ n
  (fact 'nn-in-rr 'n)
  (fact 'nn-succ-plus-one 'n)
  (have! (list '< 'n (list 'SUCC 'n))
         (lambda () (subst (list '= (list 'SUCC 'n) (list '+ 'n 1)))
                    (fact 'rr-one-in)
                    (ineq-on! (list 'IN 'n 'RR))))
  ;; n in interval(0, succ n)
  (fact 'nn-zero-le 'n)
  (fact 'nn-le-succ 'n)
  (have! (list 'IN 'n (list 'INTERVAL 0 (list 'SUCC 'n)))
         (lambda () (mac 'interval-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  (ew 'n)))
(quietly (lambda () (di) (ass-all) (lc-focus-head! 'AND) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
;; ============ BRANCH A:  x <= p(n).  Sub-split on whether n is 0. ============
(quietly (lambda ()
  (dk-focus! (car (proof-leaves)))
  (use-em '(= n 0))))
;; ---- A-zero:  n = 0, so p(n) = p(0) = a <= x, and i_ := n works ----
(quietly (lambda ()
  (dk-focus! (find-first (lambda (nd) (equal? (car (dk-asms-of nd)) '(= n 0)))
                         (proof-leaves)))
  (have! (list '<= (list 'p 'n) 'x)
         (lambda () (subst '(= n 0)) (subst '(= (p 0) a)) (ass)))
  (have! (list '<= 'x (list 'p (list 'SUCC 'n)))
         (lambda () (subst (list '= (list 'p (list 'SUCC 'n)) 'b)) (ass)))
  (fact 'nn-in-rr 'n)
  (fact 'nn-succ-plus-one 'n)
  (have! (list '< 'n (list 'SUCC 'n))
         (lambda () (subst (list '= (list 'SUCC 'n) (list '+ 'n 1)))
                    (fact 'rr-one-in)
                    (ineq-on! (list 'IN 'n 'RR))))
  (fact 'nn-zero-le 'n)
  (fact 'nn-le-succ 'n)
  (have! (list 'IN 'n (list 'INTERVAL 0 (list 'SUCC 'n)))
         (lambda () (mac 'interval-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  (ew 'n)
  (di) (ass-all) (lc-focus-head! 'AND) (di) (ass-all)
  (lc-focus-head! 'AND) (di) (ass-all)))
;; ---- A-pos:  1 <= n, so the SAME p is a partition of [a, p(n)] with n
;; ---- pieces and the induction hypothesis applies. ----
(quietly (lambda () (dk-focus! (car (proof-leaves)))))
(quietly (lambda ()
  (fact 'nn-pos-of-nonzero 'n)
  (fact 'nn-lt-succ-le 0 'n)))
(quietly (lambda ()
  ;; succ(0) <= n  is  1 <= n
  (have! '(= 1 (SUCC 0)) (lambda () (arith)))
  (have! '(<= 1 n) (lambda () (subst '(= 1 (SUCC 0))) (ass)))
  ;; 0 and n both index the big partition
  (fact 'nn-zero-le 'n)
  (fact 'nn-le-succ 'n)
  (have! (list 'IN 'n (list 'INTERVAL 0 (list 'SUCC 'n)))
         (lambda () (mac 'interval-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  (fact 'nn-zero-le (list 'SUCC 'n))
  (fact 'nn-zero-in)
  (fact 'nn-le-refl 0)
  (have! (list 'IN 0 (list 'INTERVAL 0 (list 'SUCC 'n)))
         (lambda () (mac 'interval-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  ;; a < p(n), from monotonicity at 0 < n
  (have! (list 'AND (list 'IN 0 (list 'INTERVAL 0 (list 'SUCC 'n)))
                    (list 'AND (list 'IN 'n (list 'INTERVAL 0 (list 'SUCC 'n)))
                               (list '< 0 'n)))
         (lambda () (di) (ass-all) (lc-focus-head! 'AND) (di) (ass-all)))
  (inst+ (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                  (let scan ((f g))
                                    (cond ((equal? f '(INTERVAL 0 (SUCC n))) #t)
                                          ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                          (else #f)))))) 0)))
(quietly (lambda ()
  (inst+ (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                  (let scan ((f g))
                                    (cond ((equal? f '(p 0)) #t)
                                          ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                          (else #f)))))) 'n)
  ;; p(0) < p(n) with p(0) = a  gives  a < p(n)
  (have! (list '< 'a (list 'p 'n))
         (lambda () (subst '(= a (p 0))) (ass)))))
(have! (list 'IS-PARTITION 'p 'n 'a (list 'p 'n))
  (lambda ()
    (mac 'is-partition)
    ;; nine conjuncts; eight are already in context, the ninth is monotonicity
    ;; on the SMALLER index range and is the only one with content.
    (let sweep ((k 0))
      (if (< k 8)
          (begin (di) (ass-all)
                 (if (find-first (lambda (nd) (let ((g (wff-formula (sequent-node-assertion nd))))
                                                (and (pair? g) (eq? (car g) 'AND))))
                                 (proof-leaves))
                     (lc-focus-head! 'AND))
                 (sweep (+ k 1)))))
    ;; p(n) = p(n): definedness, and p(n) is a real.
    (lc-focus-head! '=)
    (rfl)
    ;; monotonicity on the SMALLER range: the same clause with both indices
    ;; lifted from interval(0,n) into interval(0,succ n).
    (lc-focus-head! 'FORALL)
    (di) (di)
    ;; the guard `i_ in I and j_ in I and i_ < j_' lands as ONE conjunction
    (dk-split! (car (dk-asms)))
    (let ((lift! (lambda (v)
                   (mac-h 'interval-membership (list 'IN v (list 'INTERVAL 0 'n)))
                   (dk-split! (lc-asm (lambda (g) (and (pair? g) (eq? (caar (list g)) 'AND)
                                                       (equal? (cadr g) (list 'IN v 'NN))))))
                   (fact 'nn-in-rr v)
                   (have! (list '<= v (list 'SUCC 'n))
                          (lambda () (ineq-on! (list '<= v 'n) (list '<= 'n (list 'SUCC 'n)))))
                   (have! (list 'IN v (list 'INTERVAL 0 (list 'SUCC 'n)))
                          (lambda () (mac 'interval-membership) (di) (ass-all)
                                     (lc-focus-head! 'AND) (di) (ass-all))))))
      (fact 'nn-le-succ 'n)
      (fact 'nn-in-rr 'n)
      (fact 'nn-in-rr (list 'SUCC 'n))
      (lift! 'i_) (lift! 'j_))
    (have! (list 'AND (list 'IN 'i_ (list 'INTERVAL 0 (list 'SUCC 'n)))
                      (list 'AND (list 'IN 'j_ (list 'INTERVAL 0 (list 'SUCC 'n)))
                                 (list '< 'i_ 'j_)))
           (lambda () (di) (ass-all) (lc-focus-head! 'AND) (di) (ass-all)))
    ;; the UN-instantiated monotonicity clause: two nested binders.  Without
    ;; that test this matched the copy already instantiated at 0 above, which
    ;; also mentions interval(0, succ n).
    (inst+ (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                    (pair? (caddr g)) (eq? (car (caddr g)) 'FORALL)
                                    (let scan ((f g))
                                      (cond ((equal? f '(INTERVAL 0 (SUCC n))) #t)
                                            ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                            (else #f)))))) 'i_)
    (inst+ (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                    (let scan ((f g))
                                      (cond ((equal? f '(p i_)) #t)
                                            ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                            (else #f)))))) 'j_)
    (ass)))
(quietly (lambda ()
  ;; x lies in [a, p(n)]
  (have! (list 'IN 'x (list 'CCINT 'a (list 'p 'n)))
         (lambda () (mac 'ccint-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  ;; the induction hypothesis, at (p, a, p(n), x)
  (inst+ (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                  (let scan ((f g))
                                    (cond ((eq? f 'IS-PARTITION) #t)
                                          ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                          (else #f)))))) 'p)))
(quietly (lambda ()
  (inst+ 1 'a) (inst+ 1 (list 'p 'n)) (inst+ 1 'x)))
(define ii #f)
(quietly (lambda ()
  (let ((before (free-vars (car (dk-asms)))))
    (ai 1)
    (let* ((after (free-vars (car (dk-asms))))
           (new (filter (lambda (v) (not (memq v before))) after)))
      (if (not (= 1 (length new))) (error "expected one eigenvariable" new))
      (set! ii (car new))))
  (dk-split! (car (dk-asms)))))
(quietly (lambda ()
  ;; lift it out of interval(0,n) into interval(0, succ n)
  (mac-h 'interval-membership (list 'IN ii (list 'INTERVAL 0 'n)))
  (dk-split! (lc-asm (lambda (g) (and (pair? g) (eq? (car g) 'AND)
                                      (equal? (cadr g) (list 'IN ii 'NN))))))
  (fact 'nn-in-rr ii)
  (fact 'nn-in-rr 'n)
  (fact 'nn-in-rr (list 'SUCC 'n))
  (fact 'nn-le-succ 'n)
  (have! (list '<= ii (list 'SUCC 'n))
         (lambda () (ineq-on! (list '<= ii 'n) (list '<= 'n (list 'SUCC 'n)))))
  (have! (list 'IN ii (list 'INTERVAL 0 (list 'SUCC 'n)))
         (lambda () (mac 'interval-membership) (di) (ass-all)
                    (lc-focus-head! 'AND) (di) (ass-all)))
  (have! (list '< ii (list 'SUCC 'n))
         (lambda () (ineq-on! (list '< ii 'n) (list '<= 'n (list 'SUCC 'n)))))
  (ew ii)
  (di) (ass-all) (lc-focus-head! 'AND) (di) (ass-all)
  (lc-focus-head! 'AND) (di) (ass-all)))
(if (null? (proof-leaves)) (qed 'partition-locates-point))
