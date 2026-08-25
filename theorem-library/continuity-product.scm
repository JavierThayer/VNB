;;; continuity-product.scm -- the pointwise PRODUCT of two maps continuous at a
;;; point is continuous there, PROVEN, with its FUN typing.
;;;
;;;   g, h continuous at a  =>  (VNB-LAMBDA x RR (* (g x) (h x))) continuous at a
;;;
;;; The fourth of the seven `support' + `warrant! 'well-known' facts of
;;; theorem-library/continuity-algebra.scm, and the last of them that carries
;;; mathematical content (const and identity went to continuity-basics.scm, the
;;; sum to continuity-sum.scm; what remains there is composition, difference and
;;; the pointwise-equality transfer).  Statement reproduced VERBATIM, so
;;; differentiation.scm's citation reads exactly as before.
;;;
;;; WHY IT IS NOT THE SUM ARGUMENT WITH A DIFFERENT OPERATOR.  The estimate is
;;;
;;;     u*v - p*q  =  u*(v-q) + q*(u-p)
;;;
;;; -- `rr-abs-prod-bound' (theorem-library/rr-abs-basics.scm) -- so bounding
;;; |u*v - p*q| needs BOUNDS ON TWO OF THE FOUR VALUES, |u| and |q|, and not
;;; merely on the two differences.  Here u = g(a) and q = h(b): the first is at
;;; the base point and is bounded by itself, but the second is at the MOVING
;;; point and is bounded only because h is continuous.  That is the whole of the
;;; extra work over the sum -- one preliminary delta, taken at eps = 1, inside
;;; which |h(b)| <= |h(a)| + 1 by the triangle inequality.
;;;
;;; THE CONSTRUCTION.  Fix eps > 0 and put
;;;
;;;     m = |g(a)|                      bounds |g(a)|, by reflexivity
;;;     k = |h(a)| + 1                  bounds |h(b)| inside the eps=1 delta
;;;     c = m + k                       >= 1, hence positive and invertible
;;;     eta = eps * recip(c)            positive, and c * eta = eps exactly
;;;
;;; and take delta = min(min(d0, d1), d2), where d0 is h's delta at eps = 1, d1
;;; is g's delta at eta and d2 is h's delta at eta.  `rr-min-pos'
;;; (theorem-library/rr-order-basics.scm) is applied twice -- it returns a
;;; POSITIVE lower bound of two positives, which is what "the min of the deltas"
;;; means to an eps/delta proof, and it introduces no MIN operator.  Then
;;; (m+k)*eta = eps, and rr-abs-prod-bound closes the leaf in one citation.
;;;
;;; c * (eps * recip c) = eps is the one place `crs' cannot finish on its own:
;;; it decides ring identities, and c * recip c = 1 is a FIELD fact it has to be
;;; handed.  Commute by `crs', `subst' the inverse law, `crs' again -- the same
;;; three lines as sq-continuous.scm.
;;;
;;; THE ORDERING TRAPS are continuity-sum.scm's, and one more.  `mac-h' REPLACES
;;; what it unfolds, so POS-RR(eps) is unfolded only after h's delta at eps=1 has
;;; been taken, and POS-RR(eta) is BUILT (`mac pos-rr' over the unfolded `<')
;;; rather than found.  And 0 < c is reached through `rr-pos-ne-zero' rather than
;;; by unfolding `<', precisely so that the strict form rr-recip-pos wants
;;; survives the disequality rr-recip-closed wants.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after continuity-sum (same cluster), rr-abs-basics
;;; (rr-abs-prod-bound, rr-abs-mult, rr-abs-sub-sym, rr-abs-triangle-c),
;;; rr-order-basics (rr-min-pos, rr-lt-le-trans, rr-le-ne-lt), rr-recip-order
;;; (rr-zero-lt-one, rr-mul-pos, rr-recip-pos), rr-ms-dist, metric-continuity
;;; and fun-apply-type-proof -- and BEFORE continuity-algebra, whose
;;; `product-continuous-at' support it retires, and differentiation.

;;; ---- file-local driver helpers (the `cp-' prefix) --------------------

(define (cp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))

(define (cp-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 20)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cp-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cp-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (cp-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cp-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cp-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cp-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cp-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cp-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

;;; `ineq' on NAMED premises only.  The blanket "every order-shaped assumption"
;;; form used in rr-abs-basics.scm is wrong here: the context carries
;;; d(a,b) <= delta bounds whose atoms are DIST applications with no (IN _ RR)
;;; certificate, and one such premise poisons the whole call.
(define (cp-ineq . forms) (apply ineq (map cp-idx forms)))

(define (cp-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (cp-has-lambda-app? (car g)) (cp-has-lambda-app? (cdr g))))
        (else #f)))

(define (cp-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (cp-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

(define (cp-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "cp-obtain: nothing obtained for" what))
    v))

(define (cp-pos->lt! d)
  (mac-h 'pos-rr (list 'POS-RR d))
  (cp-split!)
  (have! (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))
  (fact 'rr-le-ne-lt 0 d))

;;; =====================================================================
;;; (1) x |-> g(x) * h(x) is a function RR -> RR.
;;; =====================================================================

(define cp-prod-lam '(VNB-LAMBDA x RR (* (g x) (h x))))

(sp (make-wff (forall-guarded '(g h) (list '(IN g (FUN RR RR)) '(IN h (FUN RR RR)))
                (list 'IN cp-prod-lam '(FUN RR RR)))))
(cp-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (cp-di-landed!)))))
         (fact 'fun-apply-type-c 'g 'RR 'RR z)
         (fact 'fun-apply-type-c 'h 'RR 'RR z)
         (have! (list 'AND (list 'IN (list 'g z) 'RR) (list 'IN (list 'h z) 'RR)))
         (fact 'rr-mul-closed (list 'g z) (list 'h z))
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'prod-lam-in-fun)
(topic! 'prod-lam-in-fun 'analysis)
(alias! 'prod-lam-in-fun "the pointwise product of two real functions is a function")

;;; =====================================================================
;;; (2) product-continuous-at.
;;; =====================================================================

;;; eigenvariables and derived terms, set as the proof runs
(define cp-g #f)          ; the first map
(define cp-h #f)          ; the second
(define cp-a #f)          ; the point
(define cp-e #f)          ; the eps
(define cp-m #f)          ; |g(a)|         -- bounds |g(a)|, by reflexivity
(define cp-k #f)          ; |h(a)| + 1     -- bounds |h(b)| for b near a
(define cp-c #f)          ; m + k
(define cp-eta #f)        ; eps * recip(c)
(define cp-d0 #f)         ; h's delta at eps = 1
(define cp-d1 #f)         ; g's delta at eta
(define cp-d2 #f)         ; h's delta at eta
(define cp-m1 #f)         ; a positive lower bound of d0 and d1
(define cp-dm #f)         ; ... and of that and d2: the delta

;;; Both continuity hypotheses have the same shape, so the MAP is what tells
;;; them apart; and h carries two delta-universals (at 1 and at eta), so its own
;;; delta tells those apart in turn.
(define (cp-forall-eps fn)
  (cp-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)
                     (dk-contains? f fn)))))

(define (cp-forall-delta fn d)
  (cp-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f d)
                     (dk-contains? f fn)
                     (not (dk-contains? f 'POS-RR))))))

;;; The innermost goal: d((g*h)(a), (g*h)(b)) <= eps for b within delta of a.
(define (cp-inner!)
  (let* ((landed (cp-di-landed!))
         (mem (or (find-first (lambda (x) (and (pair? x) (eq? (car x) 'IN))) landed)
                  (error "cp-inner!: no membership landed")))
         (b (cadr mem)))
    (if (not (find-first (lambda (x) (and (pair? x) (eq? (car x) '<=))) landed))
        (cp-di-landed!))
    (slot-h 'PTS mem)                     ; b in RR -- BEFORE any beta
    (cp-beta!)
    (fact 'fun-apply-type-c cp-g 'RR 'RR b)
    (fact 'fun-apply-type-c cp-h 'RR 'RR b)
    (let* ((ga (list cp-g cp-a)) (ha (list cp-h cp-a))
           (gb (list cp-g b))    (hb (list cp-h b)))
      (have! (list 'AND (list 'IN ga 'RR) (list 'IN ha 'RR)))
      (fact 'rr-mul-closed ga ha)
      (have! (list 'AND (list 'IN gb 'RR) (list 'IN hb 'RR)))
      (fact 'rr-mul-closed gb hb)
      (mac 'rr-ms-dist)              ; goal: |g(a)h(a) - g(b)h(b)| <= eps
      ;; d(a,b) <= delta, opened, and weakened to each of the three deltas
      (fact 'rr-sub-in-rr cp-a b)
      (fact 'rr-abs-closed (list '- cp-a b))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) cp-a b) cp-dm))
      (let ((adist (list '<= (list 'abs (list '- cp-a b)) cp-dm)))
        (for-each
         (lambda (pr)
           (have! (list '<= (list '(DIST RR-MS) cp-a b) (car pr))
             (lambda () (mac 'rr-ms-dist) (apply cp-ineq (cons adist (cdr pr))))))
         (list (list cp-d0 (list '<= cp-dm cp-m1) (list '<= cp-m1 cp-d0))
               (list cp-d1 (list '<= cp-dm cp-m1) (list '<= cp-m1 cp-d1))
               (list cp-d2 (list '<= cp-dm cp-d2)))))
      ;; the membership `slot-h' consumed, put back for the three instantiations
      (have! (list 'IN b '(PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
      (inst+ (cp-forall-delta cp-h cp-d0) b)          ; |h(a)-h(b)| <= 1
      (inst+ (cp-forall-delta cp-g cp-d1) b)          ; |g(a)-g(b)| <= eta
      (inst+ (cp-forall-delta cp-h cp-d2) b)          ; |h(a)-h(b)| <= eta
      (fact 'rr-sub-in-rr ga gb)
      (fact 'rr-sub-in-rr ha hb)
      (fact 'rr-sub-in-rr hb ha)
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) ha hb) 1))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) ga gb) cp-eta))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) ha hb) cp-eta))
      ;; |h(b)| <= |h(a)| + 1: the triangle inequality at (h(b)-h(a)) + h(a).
      ;; The rewriting is done OUTSIDE the abs -- `crs' proves the sum is h(b),
      ;; Leibniz lifts that to the absolute values, and the oracle chains the
      ;; equation with the inequality.
      (fact 'rr-abs-closed (list '- hb ha))
      (fact 'rr-abs-closed (list '- ha hb))
      (fact 'rr-abs-closed hb)
      (have! (list 'AND (list 'IN (list '- hb ha) 'RR) (list 'IN ha 'RR)))
      (fact 'rr-add-closed (list '- hb ha) ha)
      (fact 'rr-abs-closed (list '+ (list '- hb ha) ha))
      (fact 'rr-abs-sub-sym ha hb)
      (fact 'rr-abs-triangle-c (list '- hb ha) ha)
      (have! (list '= (list '+ (list '- hb ha) ha) hb) (lambda () (crs)))
      (have! (list '= (list 'abs (list '+ (list '- hb ha) ha)) (list 'abs hb))
             (lambda () (subst (list '= (list '+ (list '- hb ha) ha) hb)) (rfl)))
      (have! (list '<= (list 'abs hb) cp-k)
        (lambda ()
          (cp-ineq (list '<= (list 'abs (list '- ha hb)) 1)
                   (list '= (list 'abs (list '- ha hb)) (list 'abs (list '- hb ha)))
                   (list '<= (list 'abs (list '+ (list '- hb ha) ha))
                             (list '+ (list 'abs (list '- hb ha)) (list 'abs ha)))
                   (list '= (list 'abs (list '+ (list '- hb ha) ha)) (list 'abs hb)))))
      ;; |g(a)| <= m is reflexivity, m BEING |g(a)|
      (fact 'rr-abs-closed ga)
      (fact 'rr-leq-reflexive (list 'abs ga))
      ;; ... and the whole of the estimate, in one citation
      (have! (list 'AND
                   (list 'AND
                         (list 'AND (list '<= (list 'abs ga) cp-m)
                                    (list '<= (list 'abs hb) cp-k))
                         (list 'AND (list '<= (list 'abs (list '- ga gb)) cp-eta)
                                    (list '<= (list 'abs (list '- ha hb)) cp-eta)))
                   (list '<= (list '* (list '+ cp-m cp-k) cp-eta) cp-e)))
      (fact 'rr-abs-prod-bound ga ha gb hb cp-m cp-k cp-eta cp-e)
      (ass))))

;;; The eps branch: bound h near a, build eta, take three deltas, merge them.
(define (cp-eps!)
  (let* ((pos (car (cp-di-landed!)))
         (eps (cadr pos)))
    (set! cp-e eps)
    (set! cp-eta (list '* eps (list 'recip cp-c)))
    ;; h's delta at eps = 1 -- taken while POS-RR(eps) is still FOLDED, since
    ;; the instantiation is at 1 and the unfolding below is destructive.
    (have! '(POS-RR 1) (lambda () (mac 'pos-rr) (cp-goal-and! (lambda () (arith)))))
    (set! cp-d0 (cp-obtain 'd0 (lambda () (inst+ (cp-forall-eps cp-h) 1))))
    (cp-pos->lt! eps)
    ;; c = |g(a)| + (|h(a)| + 1) is at least 1, hence positive and invertible
    (have! (list 'AND (list 'IN (list 'abs (list cp-h cp-a)) 'RR) '(IN 1 RR)))
    (fact 'rr-add-closed (list 'abs (list cp-h cp-a)) 1)
    (have! (list 'AND (list 'IN cp-m 'RR) (list 'IN cp-k 'RR)))
    (fact 'rr-add-closed cp-m cp-k)
    (fact 'rr-zero-lt-one)
    (have! (list '<= 1 cp-c)
      (lambda () (cp-ineq (list '<= 0 (list 'abs (list cp-g cp-a)))
                          (list '<= 0 (list 'abs (list cp-h cp-a))))))
    (have! (list 'AND (list '< 0 1) (list '<= 1 cp-c)))
    (fact 'rr-lt-le-trans 0 1 cp-c)
    ;; the disequality WITHOUT unfolding `<': rr-recip-pos still wants the
    ;; strict form, and `mac-h' would have replaced it.
    (fact 'rr-pos-ne-zero cp-c)
    (have! (list 'AND (list 'IN cp-c 'RR) (list 'NOT (list '= cp-c 0))))
    (fact 'rr-recip-closed cp-c)
    (fact 'rr-recip-inverse cp-c)
    (fact 'rr-recip-pos cp-c)
    ;; eta = eps * recip(c), positive, with c * eta = eps
    (have! (list 'AND (list 'IN eps 'RR) (list 'IN (list 'recip cp-c) 'RR)))
    (fact 'rr-mul-closed eps (list 'recip cp-c))
    (fact 'rr-mul-pos eps (list 'recip cp-c))
    (have! (list '= (list '* cp-c cp-eta) (list '* eps (list '* cp-c (list 'recip cp-c))))
           (lambda () (crs)))
    (have! (list '= (list '* cp-c cp-eta) eps)
      (lambda ()
        (subst (list '= (list '* cp-c cp-eta)
                        (list '* eps (list '* cp-c (list 'recip cp-c)))))
        (subst (list '= (list '* cp-c (list 'recip cp-c)) 1))
        (crs)))
    (have! (list 'AND (list 'IN cp-c 'RR) (list 'IN cp-eta 'RR)))
    (fact 'rr-mul-closed cp-c cp-eta)
    (have! (list '<= (list '* cp-c cp-eta) eps)
      (lambda () (cp-ineq (list '= (list '* cp-c cp-eta) eps))))
    ;; POS-RR(eta) is BUILT, not found: nothing produced the folded predicate.
    (mac-h '< (list '< 0 cp-eta))
    (cp-split!)
    (have! (list 'POS-RR cp-eta)
           (lambda () (mac 'pos-rr) (cp-goal-and! (lambda () (ass)))))
    (set! cp-d1 (cp-obtain 'd1 (lambda () (inst+ (cp-forall-eps cp-g) cp-eta))))
    (set! cp-d2 (cp-obtain 'd2 (lambda () (inst+ (cp-forall-eps cp-h) cp-eta))))
    (cp-pos->lt! cp-d0)
    (cp-pos->lt! cp-d1)
    (cp-pos->lt! cp-d2)
    (set! cp-m1 (cp-obtain 'min1 (lambda () (fact 'rr-min-pos cp-d0 cp-d1))))
    (set! cp-dm (cp-obtain 'min2 (lambda () (fact 'rr-min-pos cp-m1 cp-d2))))
    (mac-h '< (list '< 0 cp-dm))
    (cp-split!)
    (ew cp-dm)
    (cp-goal-and!
     (lambda ()
       (let ((g (dk-goal)))
         (cond ((eq? (car g) 'POS-RR)
                (mac 'pos-rr) (cp-goal-and! (lambda () (ass))))
               ((eq? (car g) 'FORALL) (cp-inner!))
               (else (ass))))))))

;;; ---- the proof -------------------------------------------------------

;;; Statement reproduced VERBATIM from theorem-library/continuity-algebra.scm,
;;; where it stood as a `well-known' support until 2026-08-17.
(sp (make-wff '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (* (g x) (h x))) a))))))))
(cp-peel!)

;;; The three eigenvariables read off the GOAL, never off the context: the two
;;; continuity hypotheses are the same shape and context order is not peel order.
(let* ((cp-g0 (dk-goal))
       (cp-lam (list-ref cp-g0 3))
       (cp-body (list-ref cp-lam 3)))       ; (* (g x) (h x))
  (set! cp-a (list-ref cp-g0 4))
  (set! cp-g (car (list-ref cp-body 1)))
  (set! cp-h (car (list-ref cp-body 2))))
(set! cp-m (list 'abs (list cp-g cp-a)))
(set! cp-k (list '+ (list 'abs (list cp-h cp-a)) 1))
(set! cp-c (list '+ cp-m cp-k))

(fact 'rr-zero-in)
(fact 'rr-one-in)
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cp-g cp-a))
(cp-split!)
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cp-h cp-a))
(cp-split!)
(slot-h 'PTS (list 'IN cp-g '(FUN (PTS RR-MS) (PTS RR-MS))))
(slot-h 'PTS (list 'IN cp-h '(FUN (PTS RR-MS) (PTS RR-MS))))
(slot-h 'PTS (list 'IN cp-a '(PTS RR-MS)))
(fact 'prod-lam-in-fun cp-g cp-h)
;; the two values at the base point, and their absolute values -- these are the
;; bound c is built from, so they are typed once, here, for the whole proof.
(fact 'fun-apply-type-c cp-g 'RR 'RR cp-a)
(fact 'fun-apply-type-c cp-h 'RR 'RR cp-a)
(fact 'rr-abs-closed (list cp-g cp-a))
(fact 'rr-abs-closed (list cp-h cp-a))
(fact 'rr-abs-nonneg (list cp-g cp-a))
(fact 'rr-abs-nonneg (list cp-h cp-a))

(mac 'is-continuous-at)
(cp-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (cp-eps!))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
           (else (ass))))))

(qed 'product-continuous-at)
(topic! 'product-continuous-at 'analysis)
(alias! 'product-continuous-at "the product of two continuous maps is continuous")
