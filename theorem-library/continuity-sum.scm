;;; continuity-sum.scm -- the pointwise SUM of two maps continuous at a point is
;;; continuous there, PROVEN, with its FUN typing.
;;;
;;;   g, h continuous at a  =>  (VNB-LAMBDA x RR (+ (g x) (h x))) continuous at a
;;;
;;; This was the third of the seven `support' + `warrant! 'well-known' facts in
;;; theorem-library/continuity-algebra.scm, and the first of the two that carry
;;; real content (const- and identity-continuous-at moved to
;;; theorem-library/continuity-basics.scm on the same day).  The statement is
;;; reproduced VERBATIM from continuity-algebra.scm, so differentiation.scm's
;;; citations read exactly as before.
;;;
;;; THE ARGUMENT, and where each piece comes from.  Fix eps > 0.
;;;
;;;   half   = eps/2                     `rr-pos-halvable' (theorem-library/
;;;                                       rr-halving.scm) -- POS-RR(eps) gives a
;;;                                       POSITIVE d with d + d = eps, which is
;;;                                       what the estimate wants, not a
;;;                                       quotient.
;;;   d1, d2 = the deltas of g and h at eps/2
;;;   delta  = a positive lower bound of d1 and d2   `rr-min-pos'
;;;                                      (theorem-library/rr-order-basics.scm).
;;;                                       "Take the min of the two deltas" is
;;;                                       exactly that -- a delta without
;;;                                       positivity is useless, and stating it
;;;                                       existentially introduces no MIN
;;;                                       operator.
;;;
;;; and then, for b within delta of a, the whole of the mathematics is
;;;
;;;   |g(b)-g(a)| <= eps/2,  |h(b)-h(a)| <= eps/2,  eps/2 + eps/2 = eps
;;;      =>  |(g(a)+h(a)) - (g(b)+h(b))| <= eps
;;;
;;; which is `rr-abs-sum-bound' (theorem-library/rr-abs-basics.scm), one
;;; citation.  It is stated there rather than here because it is a fact about
;;; `abs' and knows nothing about continuity; every eps/2 split of a SUM wants
;;; it.  Nothing in this file does arithmetic beyond the two `ineq' calls that
;;; weaken d(a,b) <= delta to d(a,b) <= d1 and to d(a,b) <= d2.
;;;
;;; THE TWO ORDERING TRAPS, both of which cost a run:
;;;
;;;   * `mac-h' REPLACES the assumption it unfolds.  POS-RR(eps) is what
;;;     `rr-pos-halvable' is cited against, and POS-RR(half) is what the two
;;;     eps-universals of g and h are instantiated at -- so BOTH must still be
;;;     folded when those citations happen, and only afterwards may `pos-rr' be
;;;     unfolded to reach (IN eps RR), (IN half RR) and the strict forms
;;;     `rr-min-pos' guards on.  Unfolding POS-RR(eps) first loses the halving;
;;;     never unfolding it at all loses (IN eps RR), and then the six-guard
;;;     citation of rr-abs-sum-bound silently lands the IMPLICATION instead of
;;;     the conclusion, branches away from where it shows up.
;;;   * `lam-b' must come AFTER the argument is typed in RR.  The inner
;;;     universal is guarded in PTS(RR-MS), which the beta walker cannot see as
;;;     RR; fired first it still reduces but OWES (IN b RR) at a node whose
;;;     context predates b -- a leaf nothing can close, invisible until `qed'.
;;;     So: peel, `slot-h' the membership down to RR, THEN beta.  (Same trap,
;;;     same fix, as continuity-basics.scm and sq-continuous.scm.)
;;;
;;; A GUARDED macete cuts both ways here, and both directions are used:
;;; `rr-ms-dist' on a GOAL (`mac') declines silently unless both arguments are
;;; already typed in RR -- hence the four `fun-apply-type-c' citations and the
;;; two `rr-add-closed' before it -- while on a HYPOTHESIS (`mac-h') it applies
;;; and discharges the same guards from the context.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after continuity-basics (same cluster), rr-abs-basics
;;; (rr-abs-sum-bound), rr-order-basics (rr-min-pos, rr-le-ne-lt), rr-halving
;;; (rr-pos-halvable), rr-ms-dist, metric-continuity (IS-CONTINUOUS-AT),
;;; fun-apply-type-proof (fun-apply-type-c) -- and BEFORE continuity-algebra,
;;; whose `sum-continuous-at' support it retires, and differentiation.

;;; ---- file-local driver helpers (the `cs-' prefix) --------------------

(define (cs-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (cs-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (cs-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cs-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands.  A GUARDED universal goes whole; an
;;; unguarded one peels the quantifier and lands nothing, so counting `di's is
;;; not a way to reach a chosen goal.
(define (cs-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cs-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cs-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cs-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cs-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cs-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (cs-ineq . forms) (apply ineq (map cs-idx forms)))

(define (cs-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (cs-has-lambda-app? (car g)) (cs-has-lambda-app? (cdr g))))
        (else #f)))

(define (cs-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (cs-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

(define (cs-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "cs-obtain: nothing obtained for" what))
    v))

;;; POS-RR(d) opened into the typing, the two halves of `<=' /= and the strict
;;; form `rr-min-pos' guards on.  `mac-h' REPLACES POS-RR(d), so every use of
;;; the folded predicate must already have happened.
(define (cs-pos->lt! d)
  (mac-h 'pos-rr (list 'POS-RR d))
  (cs-split!)
  (have! (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))
  (fact 'rr-le-ne-lt 0 d))

;;; =====================================================================
;;; (1) x |-> g(x) + h(x) is a function RR -> RR.
;;;
;;; `lam-t' opens TWO leaves: the pointwise typing of the body and the SETHOOD
;;; of the domain -- a VNB-LAMBDA is a set of pairs, so RR must be a set before
;;; the lambda is a function at all.
;;; =====================================================================

(define cs-sum-lam '(VNB-LAMBDA x RR (+ (g x) (h x))))

(sp (make-wff (forall-guarded '(g h) (list '(IN g (FUN RR RR)) '(IN h (FUN RR RR)))
                (list 'IN cs-sum-lam '(FUN RR RR)))))
(cs-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (cs-di-landed!)))))
         (fact 'fun-apply-type-c 'g 'RR 'RR z)
         (fact 'fun-apply-type-c 'h 'RR 'RR z)
         (have! (list 'AND (list 'IN (list 'g z) 'RR) (list 'IN (list 'h z) 'RR)))
         (fact 'rr-add-closed (list 'g z) (list 'h z))
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'sum-lam-in-fun)
(topic! 'sum-lam-in-fun 'analysis)
(alias! 'sum-lam-in-fun "the pointwise sum of two real functions is a function")

;;; =====================================================================
;;; (2) sum-continuous-at.
;;; =====================================================================

;;; eigenvariables, set as the proof runs
(define cs-g #f)          ; the first map
(define cs-h #f)          ; the second
(define cs-a #f)          ; the point
(define cs-e #f)          ; the eps
(define cs-half #f)       ; eps/2
(define cs-d1 #f)         ; g's delta at eps/2
(define cs-d2 #f)         ; h's delta at eps/2
(define cs-dm #f)         ; the positive lower bound of the two

;;; The unfolded continuity of FN: forall eps. POS-RR(eps) => forsome delta ...
;;; Both hypotheses have this shape, so the map itself is the discriminator --
;;; the shape alone would match either.
(define (cs-forall-eps fn)
  (cs-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)
                     (dk-contains? f fn)))))

;;; forall b in PTS(RR-MS). d(a,b) <= D => d(fn a, fn b) <= eps/2 -- the body of
;;; the existential the eps-universal delivered.  Discriminated on the map AND on
;;; its own delta; POS-RR excluded so it cannot match the universal above.
(define (cs-forall-delta fn d)
  (cs-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f d)
                     (dk-contains? f fn)
                     (not (dk-contains? f 'POS-RR))))))

;;; The innermost goal: d((g+h)(a), (g+h)(b)) <= eps for b within delta of a.
(define (cs-inner!)
  (let* ((landed (cs-di-landed!))
         (mem (or (find-first (lambda (x) (and (pair? x) (eq? (car x) 'IN))) landed)
                  (error "cs-inner!: no membership landed")))
         (b (cadr mem)))
    ;; the distance bound arrives on the next `di' if it did not come with the
    ;; membership.
    (if (not (find-first (lambda (x) (and (pair? x) (eq? (car x) '<=))) landed))
        (cs-di-landed!))
    (slot-h 'PTS mem)                     ; b in RR -- BEFORE any beta
    (cs-beta!)
    ;; the four values, and the two sums, typed -- `mac rr-ms-dist' below is
    ;; GUARDED and declines silently without them.
    (fact 'fun-apply-type-c cs-g 'RR 'RR cs-a)
    (fact 'fun-apply-type-c cs-h 'RR 'RR cs-a)
    (fact 'fun-apply-type-c cs-g 'RR 'RR b)
    (fact 'fun-apply-type-c cs-h 'RR 'RR b)
    (let ((ga (list cs-g cs-a)) (ha (list cs-h cs-a))
          (gb (list cs-g b))    (hb (list cs-h b)))
      (have! (list 'AND (list 'IN ga 'RR) (list 'IN ha 'RR)))
      (fact 'rr-add-closed ga ha)
      (have! (list 'AND (list 'IN gb 'RR) (list 'IN hb 'RR)))
      (fact 'rr-add-closed gb hb)
      (mac 'rr-ms-dist)                   ; goal: |(g a + h a) - (g b + h b)| <= eps
      ;; d(a,b) <= delta, opened, and weakened to each of the two deltas
      (fact 'rr-sub-in-rr cs-a b)
      (fact 'rr-abs-closed (list '- cs-a b))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) cs-a b) cs-dm))
      (have! (list '<= (list '(DIST RR-MS) cs-a b) cs-d1)
        (lambda () (mac 'rr-ms-dist)
                   (cs-ineq (list '<= (list 'abs (list '- cs-a b)) cs-dm)
                            (list '<= cs-dm cs-d1))))
      (have! (list '<= (list '(DIST RR-MS) cs-a b) cs-d2)
        (lambda () (mac 'rr-ms-dist)
                   (cs-ineq (list '<= (list 'abs (list '- cs-a b)) cs-dm)
                            (list '<= cs-dm cs-d2))))
      ;; the membership `slot-h' consumed, put back for the two instantiations
      (have! (list 'IN b '(PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
      (inst+ (cs-forall-delta cs-g cs-d1) b)
      (inst+ (cs-forall-delta cs-h cs-d2) b)
      (fact 'rr-sub-in-rr ga gb)
      (fact 'rr-sub-in-rr ha hb)
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) ga gb) cs-half))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) ha hb) cs-half))
      ;; ... and the whole of the estimate, in one citation
      (have! (list 'AND
                   (list 'AND (list '<= (list 'abs (list '- ga gb)) cs-half)
                              (list '<= (list 'abs (list '- ha hb)) cs-half))
                   (list '= (list '+ cs-half cs-half) cs-e)))
      (fact 'rr-abs-sum-bound ga ha gb hb cs-half cs-e)
      (ass))))

;;; The eps branch: halve, take a delta from each map, merge them.
(define (cs-eps!)
  (let* ((pos (car (cs-di-landed!)))
         (eps (cadr pos)))
    (set! cs-e eps)
    ;; FOLDED POS-RR is what these three citations need; the unfolding comes
    ;; after all of them, `mac-h' being destructive.
    (set! cs-half (cs-obtain 'half (lambda () (fact 'rr-pos-halvable eps))))
    (set! cs-d1 (cs-obtain 'd1 (lambda () (inst+ (cs-forall-eps cs-g) cs-half))))
    (set! cs-d2 (cs-obtain 'd2 (lambda () (inst+ (cs-forall-eps cs-h) cs-half))))
    ;; (IN eps RR) is NOT optional: it is the sixth guard of rr-abs-sum-bound,
    ;; and without it that citation lands the implication and not the bound.
    (cs-pos->lt! eps)
    (cs-pos->lt! cs-half)
    (cs-pos->lt! cs-d1)
    (cs-pos->lt! cs-d2)
    (set! cs-dm (cs-obtain 'min (lambda () (fact 'rr-min-pos cs-d1 cs-d2))))
    (mac-h '< (list '< 0 cs-dm))          ; POS-RR(delta) wants the two halves
    (cs-split!)
    (ew cs-dm)
    (cs-goal-and!
     (lambda ()
       (let ((g (dk-goal)))
         (cond ((eq? (car g) 'POS-RR)
                (mac 'pos-rr) (cs-goal-and! (lambda () (ass))))
               ((eq? (car g) 'FORALL) (cs-inner!))
               (else (ass))))))))

;;; ---- the proof -------------------------------------------------------

;;; Statement reproduced VERBATIM from theorem-library/continuity-algebra.scm,
;;; where it stood as a `well-known' support until 2026-08-17.
(sp (make-wff '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (+ (g x) (h x))) a))))))))
(cs-peel!)

;;; Read the three eigenvariables off the GOAL, never off the context: the two
;;; continuity hypotheses are the same shape and the context order is not the
;;; peel order.  The goal names all three in their roles.
(let* ((cs-g0 (dk-goal))                  ; (IS-CONTINUOUS-AT RR-MS RR-MS LAM a)
       (cs-lam (list-ref cs-g0 3))
       (cs-body (list-ref cs-lam 3)))     ; (+ (g x) (h x))
  (set! cs-a (list-ref cs-g0 4))
  (set! cs-g (car (list-ref cs-body 1)))
  (set! cs-h (car (list-ref cs-body 2))))

(fact 'rr-zero-in)                        ; the (IN 0 RR) guard of rr-le-ne-lt
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cs-g cs-a))
(cs-split!)
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cs-h cs-a))
(cs-split!)
;; PTS(RR-MS) down to RR, on all three typings the unfolds landed
(slot-h 'PTS (list 'IN cs-g '(FUN (PTS RR-MS) (PTS RR-MS))))
(slot-h 'PTS (list 'IN cs-h '(FUN (PTS RR-MS) (PTS RR-MS))))
(slot-h 'PTS (list 'IN cs-a '(PTS RR-MS)))
(fact 'sum-lam-in-fun cs-g cs-h)

(mac 'is-continuous-at)
(cs-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (cs-eps!))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
           (else (ass))))))

(qed 'sum-continuous-at)
(topic! 'sum-continuous-at 'analysis)
(alias! 'sum-continuous-at "the sum of two continuous maps is continuous")
