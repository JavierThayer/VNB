;;; neg-continuous.scm -- NEGATION preserves membership in FUN(RR,RR) and
;;; continuity, PROVEN.
;;;
;;;   neg-fun-in-fun     f in FUN(RR,RR)  =>  (z |-> -f(z)) in FUN(RR,RR)
;;;   neg-continuous-at  ... and it is continuous wherever f is.
;;;
;;; WHY THESE TWO AND NOT `sub-continuous-at' (2026-08-17).  At the time,
;;; theorem-library/continuity-algebra.scm ASSERTED a difference-of-continuous
;;; support, warranted `well-known'.  Citing it to derive the min form of the
;;; Extreme Value Theorem from the max form would have put a fresh asserted leaf
;;; into the eleven bills the max form had just been removed from -- exactly the
;;; trade the work was meant to avoid.  Negation alone is far less than a
;;; difference, and it is provable outright: the two distances are EQUAL, so the
;;; delta that works for f works unchanged for -f, and no eps/2 split is needed.
;;;
;;; THAT DECISION THEN PAID A SECOND TIME, and the other way round (2026-08-18):
;;; `sub-continuous-at' is now PROVEN, in theorem-library/continuity-sub.scm,
;;; and it is proven FROM THIS FILE -- neg-continuous-at, then
;;; sum-continuous-at, then cont-transfer-ptwise-eq.  The difference never
;;; needed an eps/2 estimate of its own.  This file consequently MOVED earlier
;;; in load.scm (from just before evt-min-proof to just before continuity-sum),
;;; since continuity-sub must precede continuity-algebra; nothing in it changed.
;;;
;;; THE PROOF.  `lam-t' reduces the typing goal to "-f(z) is real for real z",
;;; which is fun-apply-type-c and rr-neg-closed.  For continuity, unfold
;;; IS-CONTINUOUS-AT on both sides, take the SAME delta, `lam-b' the two
;;; applications of the lambda (both arguments are typed in RR first -- a
;;; lambda is defined only on its domain, and reducing before the typing is
;;; evident leaves the typing owed as a stray leaf), and then the goal
;;; |-f(x) - -f(y)| <= eps and the hypothesis |f(x) - f(y)| <= eps are the same
;;; pair of linear bounds once `rr-abs-bound' has opened both.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after rr-ms-dist, rr-abs-basics (rr-abs-bound), metric-continuity,
;;; binary-minus-laws (rr-sub-in-rr) and driver-kit.

;;; ---- file-local driver helpers (the `nc-' prefix) --------------------

(define (nc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (nc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "nc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (nc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "nc-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (nc-ineq . forms) (apply ineq (map nc-idx forms)))

(define (nc-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (nc-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (nc-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an assumption lands (a guarded universal goes whole, an
;;; unguarded one peels the quantifier first and lands nothing).
(define (nc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "nc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

;;; Beta-reduce every lambda application left in the GOAL.  Bounded, because
;;; `lam-b' only WARNS when it cannot fire and a shape test alone would spin.
(define (nc-beta!)
  (let loop ((n 0))
    (if (and (dk-contains? (dk-goal) 'VNB-LAMBDA) (< n 6))
        (begin (lam-b) (loop (+ n 1))))))

(define (nc-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "nc-obtain: nothing obtained for" what))
    v))

;;; ---- the map ---------------------------------------------------------

(define nc-neg '(VNB-LAMBDA z_ RR (- (f z_))))

;;; =====================================================================
;;; (1) -f is a function RR -> RR.
;;; =====================================================================
(sp (make-wff (forall-guarded 'f '(IN f (FUN RR RR))
                (list 'IN nc-neg '(FUN RR RR)))))
(nc-peel!)
;; `lam-t' opens TWO leaves, not one: the pointwise typing of the body, and the
;; SETHOOD of the domain -- a VNB-LAMBDA is a set of pairs, so RR has to be a
;; set before the lambda is a function at all.
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (nc-di-landed!)))))
         (fact 'fun-apply-type-c 'f 'RR 'RR z)
         (fact 'rr-neg-closed (list 'f z))
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'neg-fun-in-fun)
(topic! 'neg-fun-in-fun 'analysis)

;;; =====================================================================
;;; (2) -f is continuous wherever f is.
;;; =====================================================================

(define nc-d #f)                        ; the delta, taken unchanged from f

(define (nc-forall-eps)
  (nc-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))

(define (nc-forall-delta)
  (nc-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f nc-d)
                     (not (dk-contains? f 'POS-RR))))))

;;; goal: forall y in PTS(RR-MS). d(x,y) <= delta => d(-f(x), -f(y)) <= eps
(define (nc-inner! eps)
  (let* ((landed (nc-di-landed!))
         (mem (or (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN))) landed)
                  (error "nc-inner!: no membership landed")))
         (y (cadr mem)))
    (if (not (find-first (lambda (a) (and (pair? a) (eq? (car a) '<=))) landed))
        (nc-di-landed!))                        ; the distance bound, if di stopped
    (inst+ (nc-forall-delta) y)                 ; d(f x, f y) <= eps
    (slot-h 'PTS mem)                           ; y in RR
    (fact 'fun-apply-type-c 'f 'RR 'RR y)
    (fact 'rr-neg-closed (list 'f y))
    (fact 'rr-neg-closed '(f x))
    (nc-beta!)
    ;; both sides down to abs, then to the same pair of linear bounds
    (fact 'rr-sub-in-rr '(f x) (list 'f y))
    (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) '(f x) (list 'f y)) eps))
    (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- '(f x) (list 'f y))) eps))
    (nc-split!)
    (fact 'rr-sub-in-rr '(- (f x)) (list '- (list 'f y)))
    (mac 'rr-ms-dist)
    (mac 'rr-abs-bound)
    (nc-goal-and!
     (lambda ()
       (nc-ineq (list '<= (list '- eps) (list '- '(f x) (list 'f y)))
                (list '<= (list '- '(f x) (list 'f y)) eps))))))

(sp (make-wff (forall-guarded '(f x)
                (list '(IN f (FUN RR RR)) '(IN x RR)
                      '(IS-CONTINUOUS-AT RR-MS RR-MS f x))
                (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS nc-neg 'x))))
(nc-peel!)
(mac-h 'is-continuous-at '(IS-CONTINUOUS-AT RR-MS RR-MS f x))
(nc-split!)
(fact 'neg-fun-in-fun 'f)
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)
(mac 'is-continuous-at)
(nc-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL)
            (let* ((pos (car (nc-di-landed!)))
                   (eps (cadr pos)))
              ;; the delta is taken BEFORE POS-RR(eps) is unfolded: `mac-h'
              ;; REPLACES the assumption it unfolds, and `inst+' needs
              ;; POS-RR(eps) verbatim in context to detach the instance.
              (set! nc-d (nc-obtain 'delta (lambda () (inst+ (nc-forall-eps) eps))))
              (mac-h 'pos-rr pos)
              (nc-split!)
              (ew nc-d)
              (nc-goal-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'FORALL) (nc-inner! eps) (ass))))))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS) (dk-contains? g 'VNB-LAMBDA))
            (slot 'PTS) (ass))
           (else (ass))))))
(qed 'neg-continuous-at)
(topic! 'neg-continuous-at 'analysis)
(alias! 'neg-continuous-at "negation of a continuous function is continuous")
