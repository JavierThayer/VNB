;;; sq-continuous.scm -- z |-> z*z is a function RR -> RR and is CONTINUOUS at
;;; every real point, PROVEN.
;;;
;;; WHY THIS FILE EXISTS.  It is step one of defining SQRT by the intermediate
;;; value theorem, and it is the step that is easy to miss: `ivt' applies to a
;;; CONTINUOUS f, and AT THE TIME (2026-08-17) every one of the seven facts in
;;; theorem-library/continuity-algebra.scm -- const-, identity-, sum-, product-,
;;; compose-, sub-continuous-at and cont-transfer-ptwise-eq -- was a `support'
;;; warranted `well-known'.  Nothing there was proven.  (Six of the seven are
;;; ALL SEVEN are proven now -- composition left for
;;; theorem-library/continuity-compose.scm on 2026-08-23.  The argument
;;; below stands as the record of why this file was written, and the file is
;;; still the right shape -- a direct proof for the squaring map is smaller than
;;; routing it through product-continuous-at.)  So defining SQRT by IVT
;;; and citing `product-continuous-at' for the squaring map would move the
;;; complex modulus family's bill from {sqrt-nonneg, sqrt-sq, sqrt-of-sq,
;;; sqrt-mono} to {product-continuous-at}: same trust tier, fewer leaves, and no
;;; actual gain.  That is relabelling debt, not clearing it.
;;;
;;; Deliberately just the SQUARE, not the whole continuity algebra.  Proving
;;; sum- and product-continuous-at would ripple into the derivative arc
;;; (theorem-library/differentiation.scm:134-135 cites both) and is worth doing,
;;; but it is a separate job and does not belong inside the SQRT construction.
;;;
;;; THE ESTIMATE, and where each piece comes from.  Fix t and eps > 0.  Put
;;;
;;;     c = 1 + |t| + |t|            (positive, and it bounds |t+y| below)
;;;     d = min(1, eps * recip(c))   (positive: `rr-min-pos')
;;;
;;; For |t - y| <= d:
;;;
;;;     |t*t - y*y| = |t-y| * |t+y|          -- a ring identity plus rr-abs-mult
;;;                <= d * c                  -- `rr-prod-le-prod'
;;;                <= eps                    -- d <= eps*recip(c), scaled by c
;;;
;;; and |t+y| <= c is LINEAR in the atoms t, y, |t|, d once rr-abs-bound has
;;; opened both sides, so `ineq' decides it: t+y = 2t - (t-y), |t| bounds t on
;;; both sides, and d <= 1.
;;;
;;; TWO LEMMAS WERE ADDED TO rr-order-basics.scm FOR THIS, and both are general:
;;; `rr-min-pos' (a POSITIVE lower bound of two positives -- what an eps/delta
;;; proof actually wants from a "min", since a delta without positivity is
;;; useless) and `rr-prod-le-prod' (0<=a<=b, 0<=u<=v give a*u <= b*v -- the step
;;; `ineq' cannot take, a product of two VARIABLES not being linear).  Every
;;; eps/delta estimate that bounds a difference by a product of two separately
;;; bounded factors needs exactly those two and nothing else.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after rr-order-basics (rr-min-pos, rr-prod-le-prod, rr-le-scale-nonneg),
;;; rr-abs-basics (rr-abs-mult, rr-abs-bound), rr-recip-order (rr-recip-pos,
;;; rr-mul-pos, rr-zero-lt-one), rr-metric-space-proof (rr-is-metric-space),
;;; rr-ms-dist and metric-continuity.

;;; ---- file-local driver helpers (the `sq-' prefix) --------------------

(define (sq-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (sq-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "sq-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (sq-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sq-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (sq-ineq . forms) (apply ineq (map sq-idx forms)))

(define (sq-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (sq-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (sq-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an assumption lands (a guarded universal goes whole; an unguarded
;;; one peels the quantifier first and lands nothing).
(define (sq-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "sq-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (sq-fvs forms) (apply append (map free-vars forms)))

(define (sq-skolem! ex)
  (let* ((fv0 (sq-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (sq-fvs (dk-asms)))))
      (if (null? fresh)
          (error "sq-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (sq-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (sq-has-lambda-app? (car g)) (sq-has-lambda-app? (cdr g))))
        (else #f)))

(define (sq-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (sq-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; 0 < u, where u > 0 is a LINEAR consequence of PREM.  The `<=' half is the
;;; oracle's; the disequality is the oracle again under `di' -- from 0 = u and
;;; PREM it derives 0 = 1, which the context's (NOT (= 0 1)) refutes.
(define (sq-lt-pos! u . prem)
  (have! (list '< 0 u)
    (lambda ()
      (mac '<)
      (sq-goal-and!
       (lambda ()
         (let ((g (dk-goal)))
           (if (and (pair? g) (eq? (car g) 'NOT))
               (begin (di)
                      (have! '(= 0 1)
                        (lambda () (apply sq-ineq (cons (list '= 0 u) prem))))
                      (ai '(NOT (= 0 1))))
               (apply sq-ineq prem))))))))

;;; ---- the map ---------------------------------------------------------

(define sq-lam '(VNB-LAMBDA z_ RR (* z_ z_)))

;;; =====================================================================
;;; (1)  z |-> z*z  is a function RR -> RR.
;;; =====================================================================
(sp (make-wff (list 'IN sq-lam '(FUN RR RR))))
;; `lam-t' opens TWO leaves: the pointwise typing of the body and the SETHOOD of
;; the domain -- a VNB-LAMBDA is a set of pairs, so RR must be a set before the
;; lambda is a function at all.
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (sq-di-landed!)))))
         (have! (list 'AND (list 'IN z 'RR) (list 'IN z 'RR)))
         (fact 'rr-mul-closed z z)
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'sq-fun-in-fun)
(topic! 'sq-fun-in-fun 'analysis)

;;; =====================================================================
;;; (2)  ... and it is continuous at every real point.
;;; =====================================================================

;;; eigenvariables, set as the proof runs
(define sq-t #f)          ; the point
(define sq-c #f)          ; 1 + |t| + |t|, the bound on |t + y|
(define sq-e #f)          ; the eps
(define sq-d #f)          ; the delta

(define (sq-forall-eps)
  (sq-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))

;;; The innermost goal: |t*t - y*y| <= eps for y within delta of t.
(define (sq-inner!)
  (let* ((landed (sq-di-landed!))
         (mem (or (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN))) landed)
                  (error "sq-inner!: no membership landed")))
         (y (cadr mem)))
    ;; the distance bound arrives on the next `di' if it did not come with the
    ;; membership.
    (if (not (find-first (lambda (a) (and (pair? a) (eq? (car a) '<=))) landed))
        (sq-di-landed!))
    (slot-h 'PTS mem)                                   ; y in RR
    ;; ONLY NOW may the squares be beta-reduced.  `lam-b' needs its argument
    ;; TYPED and needs it BEFORE the reduction; the enclosing binder guards y in
    ;; PTS(RR-MS), not in RR, so a `sq-beta!' run before this `slot-h' -- which
    ;; is where it used to sit, up in sq-eps! -- still fires but OWES (IN y RR)
    ;; as an extra leaf, posted at a node whose context predates y entirely.
    ;; That leaf has y FREE and no hypothesis about it: it is not provable, and
    ;; it is invisible until `qed'.
    (sq-beta!)
    (let* ((dif (list '- sq-t y))
           (sum (list '+ sq-t y))
           (adif (list 'abs dif))
           (asum (list 'abs sum)))
      (fact 'rr-sub-in-rr sq-t y)
      (have! (list 'AND (list 'IN sq-t 'RR) (list 'IN y 'RR)))
      (fact 'rr-add-closed sq-t y)
      ;; unpack d(t,y) <= delta into the two linear bounds
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) sq-t y) sq-d))
      (mac-h 'rr-abs-bound (list '<= adif sq-d))
      (sq-split!)
      ;; ... and put the abs form back, since both are wanted
      (have! (list '<= adif sq-d)
        (lambda () (mac 'rr-abs-bound)
                   (sq-goal-and!
                    (lambda () (sq-ineq (list '<= (list '- sq-d) dif)
                                        (list '<= dif sq-d))))))
      ;; |t + y| <= c : linear in t, y, |t| and delta once both sides are open
      (have! (list '<= asum sq-c)
        (lambda () (mac 'rr-abs-bound)
                   (sq-goal-and!
                    (lambda () (sq-ineq (list '<= (list '- sq-d) dif)
                                        (list '<= dif sq-d)
                                        (list '<= sq-d 1)
                                        (list '<= (list '- (list 'abs sq-t)) sq-t)
                                        (list '<= sq-t (list 'abs sq-t)))))))
      (fact 'rr-abs-closed dif)
      (fact 'rr-abs-closed sum)
      (fact 'rr-abs-nonneg dif)
      (fact 'rr-abs-nonneg sum)
      ;; |t-y| * |t+y| <= delta * c
      (have! (list 'AND (list 'AND (list '<= 0 adif) (list '<= adif sq-d))
                        (list 'AND (list '<= 0 asum) (list '<= asum sq-c))))
      (fact 'rr-prod-le-prod adif sq-d asum sq-c)
      ;; delta * c <= eps
      (have! (list 'AND (list 'IN sq-d 'RR) (list 'IN sq-c 'RR)))
      (fact 'rr-mul-closed sq-d sq-c)
      (have! (list 'AND (list 'IN sq-c 'RR) (list 'IN sq-d 'RR)))
      (fact 'rr-mul-closed sq-c sq-d)
      (have! (list '= (list '* sq-d sq-c) (list '* sq-c sq-d)) (lambda () (crs)))
      (have! (list 'AND (list '<= 0 sq-c)
                        (list '<= sq-d (list '* sq-e (list 'recip sq-c)))))
      (fact 'rr-le-scale-nonneg sq-c sq-d (list '* sq-e (list 'recip sq-c)))
      (have! (list '= (list '* sq-c (list '* sq-e (list 'recip sq-c)))
                      (list '* sq-e (list '* sq-c (list 'recip sq-c))))
             (lambda () (crs)))
      ;; c * (eps * recip c) = eps.  `crs' cannot do this on its own -- it
      ;; decides ring identities, and c * recip c = 1 is a FIELD fact it has to
      ;; be handed.  So: commute by crs, substitute the inverse law, then crs.
      (have! (list '= (list '* sq-c (list '* sq-e (list 'recip sq-c))) sq-e)
        (lambda ()
          (subst (list '= (list '* sq-c (list '* sq-e (list 'recip sq-c)))
                          (list '* sq-e (list '* sq-c (list 'recip sq-c)))))
          (subst (list '= (list '* sq-c (list 'recip sq-c)) 1))
          (crs)))
      (have! (list '<= (list '* sq-d sq-c) sq-e)
        (lambda ()
          (subst (list '= (list '* sq-d sq-c) (list '* sq-c sq-d)))
          (subst (list '= sq-e (list '* sq-c (list '* sq-e (list 'recip sq-c)))))
          (ass)))
      ;; assemble.  `rr-ms-dist' is GUARDED on both arguments being real, and
      ;; `mac' declines silently when a guard is not in context -- so the two
      ;; squares must be typed before the distance can be opened at all.  (The
      ;; hypothesis side did not need this: `mac-h' spawns the side condition as
      ;; a subgoal instead of declining.)
      (have! (list 'AND (list 'IN sq-t 'RR) (list 'IN sq-t 'RR)))
      (fact 'rr-mul-closed sq-t sq-t)
      (have! (list 'AND (list 'IN y 'RR) (list 'IN y 'RR)))
      (fact 'rr-mul-closed y y)
      (mac 'rr-ms-dist)
      (have! (list '= (list '- (list '* sq-t sq-t) (list '* y y))
                      (list '* dif sum))
             (lambda () (crs)))
      (subst (list '= (list '- (list '* sq-t sq-t) (list '* y y)) (list '* dif sum)))
      ;; rr-abs-mult guards on a CONJUNCTION, and `fact' will not split one:
      ;; without the AND in context it lands the IMPLICATION, the equation never
      ;; arrives, and the `subst' below is a warn-only no-op.
      (have! (list 'AND (list 'IN dif 'RR) (list 'IN sum 'RR)))
      (fact 'rr-abs-mult dif sum)
      (subst (list '= (list 'abs (list '* dif sum)) (list '* adif asum)))
      (have! (list 'AND (list 'IN adif 'RR) (list 'IN asum 'RR)))
      (fact 'rr-mul-closed adif asum)
      (have! (list 'AND (list 'IN (list '* adif asum) 'RR)
                        (list 'AND (list 'IN (list '* sq-d sq-c) 'RR)
                                   (list 'IN sq-e 'RR))))
      (have! (list 'AND (list '<= (list '* adif asum) (list '* sq-d sq-c))
                        (list '<= (list '* sq-d sq-c) sq-e)))
      (fact 'rr-leq-transitive (list '* adif asum) (list '* sq-d sq-c) sq-e)
      (ass))))

;;; The eps branch: choose c, then delta, then hand off to sq-inner!.
(define (sq-eps!)
  (let* ((pos (car (sq-di-landed!)))
         (eps (cadr pos)))
    (set! sq-e eps)
    ;; the continuity instance is taken from the eps-forall BEFORE POS-RR(eps)
    ;; is unfolded -- `mac-h' REPLACES what it unfolds.
    (mac-h 'pos-rr pos)
    (sq-split!)
    (have! (list 'AND (list '<= 0 eps) (list 'NOT (list '= 0 eps))))
    (fact 'rr-le-ne-lt 0 eps)
    ;; recip(c) and the candidate delta
    (fact 'rr-recip-pos sq-c)
    (have! (list 'AND (list 'IN sq-c 'RR) (list 'NOT (list '= sq-c 0))))
    (fact 'rr-recip-closed sq-c)
    (fact 'rr-recip-inverse sq-c)
    (fact 'rr-mul-pos eps (list 'recip sq-c))
    (fact 'rr-zero-lt-one)
    ;; the product must be TYPED before it can be named in rr-min-pos's
    ;; conjunction -- the typing is what rr-mul-closed lands, not what the
    ;; positivity fact gives.
    (have! (list 'AND (list 'IN eps 'RR) (list 'IN (list 'recip sq-c) 'RR)))
    (fact 'rr-mul-closed eps (list 'recip sq-c))
    (have! (list 'AND (list 'IN 1 'RR) (list 'IN (list '* eps (list 'recip sq-c)) 'RR)))
    (set! sq-d (sq-skolem!
                (dk-deepest
                 (lambda () (fact 'rr-min-pos 1 (list '* eps (list 'recip sq-c)))))))
    (mac-h '< (list '< 0 sq-d))
    (sq-split!)
    (ew sq-d)
    (sq-goal-and!
     (lambda ()
       (let ((g (dk-goal)))
         (cond ((eq? (car g) 'POS-RR)
                (mac 'pos-rr) (sq-goal-and! (lambda () (ass))))
               ((eq? (car g) 'FORALL) (sq-inner!))
               (else (ass))))))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff (forall-guarded 't '(IN t RR)
                (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS sq-lam 't))))
(sq-peel!)
(set! sq-t 't)
(set! sq-c '(+ 1 (+ (abs t) (abs t))))

(fact 'rr-is-metric-space)
(fact 'sq-fun-in-fun)
(have! '(NOT (= 0 1)) (lambda () (arith)))
(have! '(IN 1 RR) (lambda () (arith)))

;; |t| and the two linear bounds it puts on t
(fact 'rr-abs-closed 't)
(fact 'rr-abs-nonneg 't)
(fact 'rr-leq-reflexive '(abs t))
(mac-h 'rr-abs-bound '(<= (abs t) (abs t)))
(sq-split!)

;; c = 1 + |t| + |t| is a positive real
(have! '(AND (IN (abs t) RR) (IN (abs t) RR)))
(fact 'rr-add-closed '(abs t) '(abs t))
(have! '(AND (IN 1 RR) (IN (+ (abs t) (abs t)) RR)))
(fact 'rr-add-closed 1 '(+ (abs t) (abs t)))
(sq-lt-pos! sq-c '(<= 0 (abs t)))
;; `mac-h' REPLACES what it unfolds, so opening (0 < c) to reach the
;; disequality that rr-recip-closed / rr-recip-inverse want DESTROYS the strict
;; form that rr-recip-pos wants.  Put it back.
(mac-h '< (list '< 0 sq-c))
(sq-split!)
(fact 'neq-sym 0 sq-c)
(have! (list 'AND (list '<= 0 sq-c) (list 'NOT (list '= 0 sq-c))))
(fact 'rr-le-ne-lt 0 sq-c)

;; the continuity IFF, conjunct by conjunct
(mac 'is-continuous-at)
(sq-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (sq-eps!))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
           (else (ass))))))

;;; A GUARDED macete applied to a HYPOTHESIS does not decline -- it applies and
;;; posts its guard as a side-condition subgoal.  `rr-ms-dist' and
;;; `rr-abs-bound' are both guarded on their arguments being real, so sq-inner!
;;; leaves typing leaves behind that the linear script above walks straight
;;; past; they surface only at `qed', branches later.  Sweep whatever is open
;;; and close it on SHAPE, and ERROR on anything unrecognised or on a leaf that
;;; does not close -- a silent miss is the bug.
(define (sq-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves)))

(define (sq-in-asms? f) (if (member f (dk-asms)) #t #f))

(define (sq-close-leftover!)
  (let ((g (dk-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'IN) (equal? (caddr g) 'RR))
       (let ((v (cadr g)))
         (cond ((sq-in-asms? g) (ass))
               ((sq-in-asms? (list 'IN v '(PTS RR-MS)))
                (slot-h 'PTS (list 'IN v '(PTS RR-MS))) (ass))
               (else (error "sq-continuous: cannot type" v (dk-asms))))))
      (else (error "sq-continuous: unexpected leftover leaf" g)))))

(let close ((fuel 40) (prev #f))
  (let ((s (find-first (lambda (s) #t) (sq-open))))
    (if (and s (> fuel 0))
        (begin
          (if (eq? s prev) (error "sq-continuous: leaf did not close" (dk-goal)))
          (dk-focus! s)
          (sq-close-leftover!)
          (close (- fuel 1) s))
        #t)))

(qed 'sq-continuous-at)
(topic! 'sq-continuous-at 'analysis)
(alias! 'sq-continuous-at "continuity of the square" "z |-> z^2 is continuous")
