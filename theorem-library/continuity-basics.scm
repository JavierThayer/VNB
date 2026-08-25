;;; continuity-basics.scm -- the constant and identity maps are continuous,
;;; PROVEN, with their FUN typings.
;;;
;;; These were the first two of the seven `support' + `warrant! 'well-known'
;;; facts in theorem-library/continuity-algebra.scm, none of which was proven.
;;; They are the cheapest two -- no eps/2 split, no bound on a factor, just the
;;; definition -- and they are cited by theorem-library/differentiation.scm
;;; (:130-132, :199, :215), so retiring them takes two asserted leaves out of
;;; the Caratheodory chain-rule block.
;;;
;;;   const     any delta does; d(c,c) = |c - c| = 0 <= eps.
;;;   identity  delta = eps does; the goal after beta IS the hypothesis.
;;;
;;; THE ONE THING THAT MATTERS IN THE DRIVER, and it is the trap that cost the
;;; SQRT work a run: `lam-b' must come AFTER the argument is typed in RR, not
;;; before.  The inner universal is guarded in PTS(RR-MS), and the beta walker
;;; cannot see that as RR; fired first, it still reduces but OWES (IN y RR) at a
;;; node whose context predates y, where y is FREE -- a leaf nothing can close,
;;; invisible until `qed'.  So: peel, `slot-h' the membership down to RR, THEN
;;; beta.  (primitive-inferences.scm:1404 posts the obligation against the outer
;;; assumptions, which is why the scope is lost.)
;;;
;;; The remaining five of continuity-algebra.scm -- sum, product, compose, sub,
;;; and the pointwise-equality transfer -- are still asserted.  Sum and product
;;; are the next two and they carry the real content; `rr-min-pos' and
;;; `rr-prod-le-prod' (rr-order-basics.scm) exist for exactly them.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after rr-metric-space-proof (rr-is-metric-space), rr-ms-dist,
;;; rr-abs-basics (rr-abs-bound), metric-continuity, and BEFORE
;;; continuity-algebra (whose two supports it retires) and differentiation.

;;; ---- file-local driver helpers (the `cb-' prefix) --------------------

(define (cb-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (cb-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cb-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cb-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an assumption lands: a GUARDED universal goes whole, an unguarded
;;; one peels the quantifier and lands nothing.
(define (cb-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cb-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cb-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cb-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (cb-ineq . forms) (apply ineq (map cb-idx forms)))

(define (cb-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (cb-has-lambda-app? (car g)) (cb-has-lambda-app? (cdr g))))
        (else #f)))

(define (cb-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (cb-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; The membership the inner `di' landed, and the distance bound that follows it
;;; (which may arrive on the same call or the next one).
(define (cb-inner-point!)
  (let* ((landed (cb-di-landed!))
         (mem (or (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN))) landed)
                  (error "cb-inner-point!: no membership landed"))))
    (if (not (find-first (lambda (a) (and (pair? a) (eq? (car a) '<=))) landed))
        (cb-di-landed!))
    (slot-h 'PTS mem)                    ; y in RR -- BEFORE any beta
    (cadr mem)))

;;; ---- the two maps ----------------------------------------------------

(define cb-const '(VNB-LAMBDA x RR c))
(define cb-ident '(VNB-LAMBDA x RR x))

;;; =====================================================================
;;; (1) typings.  `lam-t' opens the pointwise typing AND the domain sethood.
;;; =====================================================================

(sp (make-wff (forall-guarded 'c '(IN c RR) (list 'IN cb-const '(FUN RR RR)))))
(cb-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (begin (cb-di-landed!) (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'const-lam-in-fun)
(topic! 'const-lam-in-fun 'analysis)

(sp (make-wff (list 'IN cb-ident '(FUN RR RR))))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (begin (cb-di-landed!) (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'ident-lam-in-fun)
(topic! 'ident-lam-in-fun 'analysis)

;;; =====================================================================
;;; (2) the constant map is continuous.  Statement byte-identical to the
;;; support it retires (continuity-algebra.scm).
;;; =====================================================================

(define (cb-const-inner! eps)
  (cb-inner-point!)
  (cb-beta!)                                   ; goal: d(c,c) <= eps
  (have! '(AND (IN c RR) (IN c RR)))
  (fact 'rr-sub-in-rr 'c 'c)
  (mac 'rr-ms-dist)
  (mac 'rr-abs-bound)
  (cb-and! (lambda () (cb-ineq (list '<= 0 eps)))))

(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (FORALL a (IMPLIES (IN a RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR c) a)))))))
(cb-peel!)
(fact 'rr-is-metric-space)
(fact 'const-lam-in-fun 'c)
(mac 'is-continuous-at)
(cb-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'FORALL)
        (let* ((pos (car (cb-di-landed!)))
               (eps (cadr pos)))
          (mac-h 'pos-rr pos)
          (cb-split!)
          ;; any positive delta serves; 1 is the cheapest to type
          (have! '(POS-RR 1) (lambda () (mac 'pos-rr) (cb-and! (lambda () (arith)))))
          (ew 1)
          (cb-and!
           (lambda ()
             (let ((h (dk-goal)))
               (cond ((eq? (car h) 'FORALL) (cb-const-inner! eps))
                     (else (ass))))))))
       ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
       (else (ass))))))
(qed 'const-continuous-at)
(topic! 'const-continuous-at 'analysis)

;;; =====================================================================
;;; (3) the identity map is continuous -- delta = eps, and after the beta the
;;; goal IS the hypothesis.
;;; =====================================================================

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR x) a)))))
(cb-peel!)
(fact 'rr-is-metric-space)
(fact 'ident-lam-in-fun)
(mac 'is-continuous-at)
(cb-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'FORALL)
        ;; POS-RR(eps) is NOT unfolded here: eps is used AS the delta, so the
        ;; folded form is what the witness conjunct needs.
        (let* ((pos (car (cb-di-landed!)))
               (eps (cadr pos)))
          (ew eps)
          (cb-and!
           (lambda ()
             (let ((h (dk-goal)))
               (cond ((eq? (car h) 'FORALL)
                      (cb-inner-point!)
                      (cb-beta!)
                      (ass))
                     (else (ass))))))))
       ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
       (else (ass))))))
(qed 'identity-continuous-at)
(topic! 'identity-continuous-at 'analysis)
