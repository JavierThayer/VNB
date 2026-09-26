;;; recip-succ-small.scm -- the eventual form of the Archimedean bound.
;;;
;;;   forall d > 0.  exists n in NN.  forall m >= n.  recip(m+1) <= d
;;;
;;; The tree ASSERTS the pointwise form (`nn-recip-succ-small', informal:
;;; "there is SOME n with recip(n+1) < eps") and proves from it that the
;;; sequence recip(k+1) converges to 0.  What an epsilon argument needs is the
;;; EVENTUAL form -- a threshold past which every index works -- and that is
;;; what this derives, out of the convergence theorem rather than by a second
;;; assertion.  Bills `modulo {nn-recip-succ-small}', trust: informal.
;;;
;;; Two helpers are exported, because the Cauchy-criterion driver needs both:
;;;   type-recip!  lands the five facts making recip(n+1) a positive real
;;;   asm-index / mentions? / focus-head!   context and leaf finders

(define (asm-index pred)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "asm-index: nothing matches"))
          ((pred (if (wff? (car as)) (wff-formula (car as)) (car as))) i)
          (else (loop (cdr as) (+ i 1))))))

(define (mentions? f sub)
  (cond ((equal? f sub) #t)
        ((pair? f) (or (mentions? (car f) sub) (mentions? (cdr f) sub)))
        (else #f)))

(define (focus-head! h)
  (dk-focus! (or (find-first (lambda (n) (let ((g (wff-formula (sequent-node-assertion n))))
                                           (and (pair? g) (eq? (car g) h))))
                             (proof-leaves))
                 (error "focus-head!: no open leaf with head" h))))

(define (focus-goal! g)
  (dk-focus! (or (find-first (lambda (n) (equal? (wff-formula (sequent-node-assertion n)) g))
                             (proof-leaves))
                 (error "focus-goal!: no open leaf with that goal" g))))

;;; The one new eigenvariable an `ai' on a context existential minted.
(define (skolem-of! k)
  (let ((before (free-vars (if (wff? (car (dk-asms))) (wff-formula (car (dk-asms))) (car (dk-asms))))))
    (ai k)
    (let* ((after (free-vars (if (wff? (car (dk-asms))) (wff-formula (car (dk-asms))) (car (dk-asms)))))
           (new   (filter (lambda (v) (not (memq v before))) after)))
      (if (not (= 1 (length new)))
          (error "skolem-of!: expected exactly one new eigenvariable" new))
      (car new))))

;;; recip(n+1) is a positive real, for n in NN.
(define (type-recip! n)
  (fact 'rr-one-in)
  (fact 'rr-zero-in)
  (fact 'nn-in-rr n)
  (fact 'nn-zero-le n)
  (have! (list 'IN (list '+ n 1) 'RR) (lambda () (in-rr)))
  (have! (list '< 0 (list '+ n 1))
         (lambda () (ineq-on! (list '<= 0 n) (list 'IN n 'RR))))
  (fact 'rr-pos-ne-zero (list '+ n 1))
  (have! (list 'AND (list 'IN (list '+ n 1) 'RR) (list 'NOT (list '= (list '+ n 1) 0)))
         (lambda () (di) (ass-all)))
  (fact 'rr-recip-closed (list '+ n 1))
  (fact 'rr-recip-pos (list '+ n 1)))

(sp (make-wff "forall([d], pos-rr(d) implies forsome([n_ in nn], forall([m_ in nn], n_ <= m_ implies recip(m_ + 1) <= d)))"))
(quietly (lambda ()
  (di) (di)
  (fact 'rr-recip-succ-converges-to-zero)
  (mac-h 'converges-to '(CONVERGES-TO RR-MS (VNB-LAMBDA k NN (RECIP (+ k 1))) 0))
  (dk-split! (car (dk-asms)))
  (inst+ (asm-index (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (mentions? f '(DIST RR-MS))))) 'd)
  (let ((wit (skolem-of! 1)))
    (dk-split! (car (dk-asms)))
    (ew wit))
  (di) (ass-all) (focus-head! 'FORALL) (di) (di)
  (inst+ (asm-index (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (mentions? f '(DIST RR-MS))))) 'm_)
  (lam-b-h 1)
  (type-recip! 'm_)
  (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) '(RECIP (+ m_ 1)) 0) 'd))
  (mac-h 'pos-rr '(POS-RR d))
  (dk-split! (car (dk-asms)))
  (have! '(IN (- (RECIP (+ m_ 1)) 0) RR) (lambda () (in-rr)))
  (mac-h 'rr-abs-bound '(<= (ABS (- (RECIP (+ m_ 1)) 0)) d))
  (dk-split! (car (dk-asms)))
  (ineq-on! (list '<= (list '- (list 'RECIP '(+ m_ 1)) 0) 'd)
            (list '<= (list '- 'd) (list '- (list 'RECIP '(+ m_ 1)) 0)))))
(qed 'recip-succ-small)
