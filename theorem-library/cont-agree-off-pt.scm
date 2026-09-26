;;; cont-agree-off-pt.scm -- two functions continuous at a point and agreeing
;;; AWAY from it agree AT it, PROVEN.
;;;
;;;   is-continuous-at(RR-MS,RR-MS,fa,pt),  is-continuous-at(...,fb,pt),
;;;   fa(x) = fb(x) for every x /= pt        =>   fa(pt) = fb(pt)
;;;
;;; The last of continuity-algebra.scm's supports but one: five of its seven
;;; were proven on 2026-08-18 through the TRANSFER mechanism, and this one and
;;; `compose-continuous-at' were left.  It was FOURTH in the sole-leaf ranking
;;; -- the leaf alone in four bills, and named in eighty-eight.
;;;
;;; THE ARGUMENT.  Given eps > 0, halve it; take a delta for each function at
;;; that half and a radius w below BOTH (`rr-min-pos', which hands back the
;;; witness directly and spares us a MIN term); sample at x = pt + w, which is
;;; within both radii and is not pt.  Then
;;;
;;;   |fa(pt) - fb(pt)|  <=  |fa(pt) - fa(x)| + |fa(x) - fb(x)| + |fb(x) - fb(pt)|
;;;                       =  |fa(pt) - fa(x)| +        0        + |fb(x) - fb(pt)|
;;;                       <=  d + d  =  eps,
;;;
;;; the middle term vanishing because x /= pt.  True of every positive eps, so
;;; the difference is 0.
;;;
;;; FOUR MECHANICS, each of which cost a run:
;;;
;;;  * `mac-h' IS DESTRUCTIVE, and `ca-open-pos!' goes through it.  Opening
;;;    POS-RR(eps) early consumed the very hypothesis `rr-pos-halvable' needed;
;;;    opening POS-RR(d) early would have consumed what the two eps-universals
;;;    detach against.  Each is opened at its point of use, not at the top.
;;;  * `rr-le-ne-lt' and `rr-min-pos' and `rr-leq-antisymmetric' all have
;;;    CONJUNCTIVE antecedents, so each wants a `have!' of the AND first.  With
;;;    `rr-le-ne-lt' the symptom was three steps away: 0 < delta never arrived,
;;;    so `rr-min-pos' landed an un-detached implication chain and the skolemizer
;;;    reported "landed no assumption".
;;;  * THE INNER UNIVERSAL IS GUARDED ON `x in PTS(RR-MS)', so the PTS form has
;;;    to be PUT BACK with a `have!' + `slot' on the goal.  `slot-h' rewrites the
;;;    hypothesis to `x in RR' -- the wrong direction here -- and the
;;;    instantiation then detaches nothing.  continuity-sum.scm meets this and
;;;    solves it the same way.
;;;  * |pt - x| = |x - pt| = |w| = w is REWRITING, not `ineq'.  The middle step
;;;    is a congruence under `abs' (x - pt IS w), and the oracle sees an `abs' as
;;;    an opaque atom, so an equation about the ARGUMENT is invisible to it.
;;;
;;; And at the end, `prop' could NOT get D = 0 from |D| = 0 through the
;;; `rr-abs-zero' iff.  The two one-sided bounds -- D <= |D| and -|D| <= D,
;;; against |D| <= 0 -- are linear, so `ineq' closes both halves and
;;; antisymmetry finishes.
;;;
;;; Loads after continuity-algebra (IS-CONTINUOUS-AT and the supports it keeps)
;;; and before differentiation, the earliest citer.  Needs rr-halving,
;;; rr-order-basics (rr-min-pos, rr-le-ne-lt, rr-le-all-pos-nonpos),
;;; rr-abs-basics and rr-ms-dist.

(define (ca-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ca-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (ca-ineq . fs) (apply ineq (map ca-idx fs)))
(define (ca-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 9) (error "ca-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))
(define (ca-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ca-find: none" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define (ca-skolem! ex)
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "ca-skolem!: nothing fresh" ex) (car fresh)))))

;; The statement, LITERALLY (it used to be read off the theorem table, which
;; found the asserted support of the same name in continuity-algebra.scm; that
;; support was retired 2026-09-16 and the lookup then failed -- CLAUDE.md's
;; "a proof file states its theorem LITERALLY").
(sp (make-wff '(FORALL fa (FORALL fb (FORALL pt (IMPLIES (IN pt RR) (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS fa pt) (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS fb pt) (IMPLIES (FORALL x (IMPLIES (IN x RR) (IMPLIES (NOT (= x pt)) (= (fa x) (fb x))))) (= (fa pt) (fb pt)))))))))))
(ca-peel-to! '=)
;; unfold both continuity hypotheses; each is used once, so the destructive
;; mac-h costs nothing here.
(dk-split! (dk-landed-find
            (lambda () (mac-h 'is-continuous-at '(IS-CONTINUOUS-AT RR-MS RR-MS fa pt)))
            (dk-head? 'AND)))
(dk-split! (dk-landed-find
            (lambda () (mac-h 'is-continuous-at '(IS-CONTINUOUS-AT RR-MS RR-MS fb pt)))
            (dk-head? 'AND)))
(define ca-agree
  (ca-find 'agree (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                   (dk-contains? a 'fa) (dk-contains? a 'fb)))))
(define (ca-eps-univ f)
  (ca-find f (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'POS-RR) (dk-contains? a f)
                              (not (dk-contains? a (if (eq? f 'fa) 'fb 'fa)))))))

;; POS-RR t  ->  t in RR, 0 <= t, 0 /= t, and the STRICT 0 < t that
;; rr-min-pos and the order lemmas want.
(define (ca-open-pos! t)
  (mac-h 'pos-rr (list 'POS-RR t))
  (dk-split! (list 'AND (list 'IN t 'RR)
                   (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t)))))
  (fact 'rr-zero-in)
  ;; rr-le-ne-lt's antecedent is a CONJUNCTION -- land the AND or `fact' keeps
  ;; the implication and 0 < t never arrives.
  (have! (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))
  (fact 'rr-le-ne-lt 0 t))

(slot-h 'PTS (list 'IN 'fa '(FUN (PTS RR-MS) (PTS RR-MS))))
(slot-h 'PTS (list 'IN 'fb '(FUN (PTS RR-MS) (PTS RR-MS))))
(fact 'fun-apply-type-c 'fa 'RR 'RR 'pt)
(fact 'fun-apply-type-c 'fb 'RR 'RR 'pt)
(fact 'rr-sub-in-rr '(fa pt) '(fb pt))
(fact 'rr-abs-closed '(- (fa pt) (fb pt)))

(have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (abs (- (fa pt) (fb pt))) eps)))
  (lambda ()
    (di) (di)
    (let* ((hex (dk-fact! 'rr-pos-halvable 'eps))
           (d   (ca-skolem! hex))
           (e1  (dk-deepest (lambda () (inst+ (ca-eps-univ 'fa) d))))
           (d1  (ca-skolem! e1))
           (e2  (dk-deepest (lambda () (inst+ (ca-eps-univ 'fb) d))))
           (d2  (ca-skolem! e2)))
      ;; d is opened only NOW: both eps-universals above were detached with
      ;; POS-RR d, which `ca-open-pos!' would have consumed.
      (ca-open-pos! d)
      (ca-open-pos! d1)
      (ca-open-pos! d2)
      (let* ((mex (dk-fact! 'rr-min-pos d1 d2))
             (w   (ca-skolem! mex))
             (x   (list '+ 'pt w)))
        (define (inner-univ dd)
          (ca-find dd (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                       (dk-contains? a dd) (dk-contains? a 'DIST)))))
        (have! (list 'AND '(IN pt RR) (list 'IN w 'RR)))
        (fact 'rr-add-closed 'pt w)
        (have! (list '= (list '- x 'pt) w) (lambda () (crs)))
        (fact 'rr-lt-implies-le 0 w)
        (fact 'rr-abs-of-nonneg w)
        (fact 'rr-sub-in-rr x 'pt)
        (fact 'rr-abs-sub-sym 'pt x)
        (for-each
         (lambda (dd)
           (have! (list '<= (list (list 'DIST 'RR-MS) 'pt x) dd)
             (lambda ()
               ;; |pt - x| = |x - pt| = |w| = w <= dd.  REWRITES, not `ineq':
               ;; the middle step is a congruence under `abs' (x - pt IS w), and
               ;; the oracle sees an abs as an opaque atom, so it cannot use an
               ;; equation about the argument.
               (mac 'rr-ms-dist)
               (subst (list '= (list 'abs (list '- 'pt x)) (list 'abs (list '- x 'pt))))
               (subst (list '= (list '- x 'pt) w))
               (subst (list '= (list 'abs w) w))
               (ass))))
         (list d1 d2))
        ;; the inner universal is guarded on `x in PTS(RR-MS)', so PUT THAT
        ;; FORM BACK rather than convert it away: `slot-h' rewrites the
        ;; hypothesis to `x in RR' and the detachment then finds nothing.
        (have! (list 'IN x '(PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
        (inst+ (inner-univ d1) x)
        (inst+ (inner-univ d2) x)
        ;; the two estimates, as absolute values
        (fact 'fun-apply-type-c 'fa 'RR 'RR x)
        (fact 'fun-apply-type-c 'fb 'RR 'RR x)
        (for-each
         (lambda (f)
           (fact 'rr-sub-in-rr (list f 'pt) (list f x))
           (fact 'rr-abs-closed (list '- (list f 'pt) (list f x)))
           (have! (list '<= (list 'abs (list '- (list f 'pt) (list f x))) d)
             (lambda () (mac 'rr-ms-dist-rev) (ass)))
           (fact 'rr-le-abs (list '- (list f 'pt) (list f x)))
           (fact 'rr-neg-abs-le (list '- (list f 'pt) (list f x))))
         '(fa fb))
        ;; the sample point differs from pt, so the two functions agree there
        (have! (list 'NOT (list '= x 'pt))
          (lambda ()
            (di)
            (have! '(<= 1 0) (lambda () (ca-ineq (list '= x 'pt) (list '< 0 w))))
            (fact 'rr-one-in) (fact 'rr-zero-in)
            (fact 'rr-zero-lt-one)
            (fact 'rr-lt-implies-le 0 1)
            (have! '(AND (IN 1 RR) (IN 0 RR)))
            (have! '(AND (<= 1 0) (<= 0 1)))
            (fact 'rr-leq-antisymmetric 1 0)
            (fact 'rr-pos-ne-zero 1)
            (ai '(NOT (= 1 0)))))
        (inst+ ca-agree x)
        ;; |fa(pt) - fb(pt)| <= d + d = eps.  `eps in RR' is opened HERE and not
        ;; earlier: `ca-open-pos!' goes through `mac-h', which REPLACES the
        ;; POS-RR hypothesis, and `rr-pos-halvable' above still needed it.
        (ca-open-pos! 'eps)
        (mac 'rr-abs-bound)
        (for-each
         (lambda (l)
           (dk-focus! l)
           (ca-ineq (list '<= (list '- '(fa pt) (list 'fa x))
                          (list 'abs (list '- '(fa pt) (list 'fa x))))
                    (list '<= (list 'abs (list '- '(fa pt) (list 'fa x))) d)
                    (list '<= (list '- (list 'abs (list '- '(fa pt) (list 'fa x))))
                          (list '- '(fa pt) (list 'fa x)))
                    (list '<= (list '- '(fb pt) (list 'fb x))
                          (list 'abs (list '- '(fb pt) (list 'fb x))))
                    (list '<= (list 'abs (list '- '(fb pt) (list 'fb x))) d)
                    (list '<= (list '- (list 'abs (list '- '(fb pt) (list 'fb x))))
                          (list '- '(fb pt) (list 'fb x)))
                    (list '= (list 'fa x) (list 'fb x))
                    (list '= (list '+ d d) 'eps)))
         (dk-opened (lambda () (di))))))))
;; a nonnegative real below every positive is 0, and a vanishing difference is
;; an equality.
(define ca-D '(- (fa pt) (fb pt)))
(fact 'rr-le-all-pos-nonpos (list 'abs ca-D))
(fact 'rr-abs-nonneg ca-D)
(fact 'rr-zero-in)
(have! (list 'AND (list 'IN (list 'abs ca-D) 'RR) '(IN 0 RR)))
(have! (list 'AND (list '<= (list 'abs ca-D) 0) (list '<= 0 (list 'abs ca-D))))
(fact 'rr-leq-antisymmetric (list 'abs ca-D) 0)
;; D = 0 WITHOUT the abs-zero iff: |D| <= 0 with the two one-sided bounds
;; D <= |D| and -|D| <= D is linear, so the oracle closes both halves and
;; antisymmetry finishes.  (Through the iff, `prop' declined.)
(fact 'rr-le-abs ca-D)
(fact 'rr-neg-abs-le ca-D)
(have! (list '<= ca-D 0)
  (lambda () (ca-ineq (list '<= ca-D (list 'abs ca-D))
                      (list '<= (list 'abs ca-D) 0))))
(have! (list '<= 0 ca-D)
  (lambda () (ca-ineq (list '<= (list '- (list 'abs ca-D)) ca-D)
                      (list '<= (list 'abs ca-D) 0))))
(have! (list 'AND (list 'IN ca-D 'RR) '(IN 0 RR)))
(have! (list 'AND (list '<= ca-D 0) (list '<= 0 ca-D)))
(fact 'rr-leq-antisymmetric ca-D 0)
(fact 'eq-sym ca-D 0)
(fact 'rr-diff-zero-eq '(fa pt) '(fb pt))
(ass)
(qed 'cont-agree-off-pt)

(topic! 'cont-agree-off-pt 'analysis)
(alias! 'cont-agree-off-pt
        "functions continuous at a point and agreeing off it agree at it")
