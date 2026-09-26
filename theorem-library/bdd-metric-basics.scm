;;; bdd-metric-basics.scm -- the t/(1+t) scalar family and the two BDD-METRIC
;;; statements that read off it, PROVEN.
;;;
;;;   bdd-fn-nonneg   0 <= t  =>  0 <= t/(1+t)
;;;   bdd-fn-lt-one   0 <= t  =>  t/(1+t) < 1
;;;   bdd-fn-le-arg   0 <= t  =>  t/(1+t) <= t
;;;   bdd-fn-mono     0 <= s <= t  =>  s/(1+s) <= t/(1+t)
;;;   bdd-fn-subadd   0 <= a, 0 <= b  =>  (a+b)/(1+a+b) <= a/(1+a) + b/(1+b)
;;;   bdd-fn-zero     t = 0  =>  t/(1+t) = 0          [new]
;;;   bdd-fn-zero-eq  t/(1+t) = 0  =>  t = 0          [new]
;;;   bdd-metric-bounded            rho(x,y) < 1
;;;   bdd-metric-is-metric-space    rho = d/(1+d) is a metric
;;;
;;; All but the last two of the bdd-fn-* were `well-known' supports in
;;; structure-library/scalar-inequalities.scm; the two BDD-METRIC statements
;;; were `well-known' supports in structure-library/bounded-metric.scm.  Every
;;; result below is `modulo 0'.
;;;
;;; ONE ENGINE, THREE PIECES, AND IT IS WHY THE WHOLE FAMILY FELL TOGETHER.
;;;
;;; (1) `bmb-one-plus!' -- the reciprocal block.  From u in RR and 0 <= u it
;;;     lands 1+u in RR, 0 < 1+u, 1+u /= 0, recip(1+u) in RR, 0 < recip(1+u),
;;;     (1+u)*recip(1+u) = 1 and u*recip(1+u) in RR.  `mac 'binary-divide-def'
;;;     (named-only, so cited by name) then turns every u/(1+u) in the goal into
;;;     A(u) := u * recip(1+u), and `ineq' reads that product as ONE ATOM
;;;     (ineq-oracle.scm: a product of two non-constant factors is a maximal
;;;     atom).  So the facts below are LINEAR in the atoms recip(1+u), A(u),
;;;     A(u)*u -- each certified in RR by a landed rr-mul-closed.
;;;
;;; (2) THE TWO IDENTITIES, both proved the way bdd-fn-reflect
;;;     (theorem-library/bdd-metric-convergence.scm) proves its own: cut the
;;;     ring-equal form that CARRIES the factor (1+u)*recip(1+u) -- `crs' closes
;;;     it, recip(1+u) being an opaque generator -- `subst' it into the goal,
;;;     then `subst' the inverse equation to collapse that factor to 1.
;;;
;;;         recip(1+u) + A(u)  =  1          (bmb-inv-id!)
;;;         A(u) + A(u)*u      =  u          (bmb-quot-id!)
;;;
;;;     nonneg, lt-one, le-arg, zero and zero-eq are each ONE Farkas step off
;;;     one of these two.
;;;
;;; (3) `bmb-cancel!' -- clearing denominators, once, for the two facts that
;;;     need it.  Goal X <= Y, with 0 < C and X*C <= Y*C in context: the
;;;     identity C*(Y-X) = Y*C - X*C is a `crs' step, `rr-nonneg-cancel-pos'
;;;     (theorem-library/rr-order-basics) takes the positive factor off, and
;;;     `ineq' finishes.  With C the product of the denominators, mono and
;;;     subadd become POLYNOMIAL inequalities that `crs' normalises:
;;;
;;;         mono:    s + s*t  <=  t + s*t
;;;         subadd:  (a+b)(1+a)(1+b)  <=  a(1+a+b)(1+b) + b(1+a+b)(1+a),
;;;                  whose difference `crs' reduces to  2ab + a^2 b + a b^2,
;;;                  three products of nonnegatives.
;;;
;;; WHAT THE ZERO LAW COST.  The triage table recorded "the zero law
;;; d/(1+d) = 0 => d = 0, for which NO bdd-fn support exists (the warrant says
;;; f(t)=0 iff t=0 and names nothing)" as the obstacle under
;;; bdd-metric-is-metric-space.  It is `bdd-fn-zero-eq', and it needs no new
;;; machinery: A = 0 forces A*t = 0 (one `subst' and `crs'), and then
;;; A + A*t = t reads t = 0.  The converse `bdd-fn-zero' is the same identity
;;; with 0 <= A and 0 <= A*t.
;;;
;;; bdd-metric-is-metric-space is then the trunc-metric-proof.scm shape
;;; (theorem-library/trunc-metric-proof.scm, the same construction for
;;; min(1,d)): unfold IS-METRIC-SPACE on the GOAL only -- every citation below
;;; is guarded on the folded IS-METRIC-SPACE(s) -- rewrite PTS(BDD-METRIC s)
;;; away with `bdd-metric-carrier', and take the four conjuncts apart.  The
;;; distance slot needs `mac 'BDD-METRIC' + `slot 'DIST' + `nth-r' rather than a
;;; bare `slot', BDD-METRIC being a def-functoid (a LIST literal) and not a
;;; def-constructed-functor: there is no per-slot projection, and `slot' alone
;;; falls through to the global accessor index.  `lam-t' then opens TWO leaves,
;;; the pointwise typing and the SETHOOD of CARTESIAN(PTS s, PTS s).
;;;
;;; WINDOW.  lo: theorem-library/bdd-metric-distance and
;;; theorem-library/bdd-metric-carrier (the two BDD-METRIC read-offs),
;;; theorem-library/rr-recip-order (rr-recip-pos, rr-mul-pos),
;;; theorem-library/rr-order-basics (rr-pos-ne-zero, rr-lt-le-trans,
;;; rr-nonneg-cancel-pos), theorem-library/op-typing (metric-dist-real),
;;; structure-library/metric-laws (the five projected laws),
;;; theorem-library/binary-minus-laws (rr-sub-in-rr).
;;; hi: theorem-library/bdd-metric-convergence, the earliest citer of
;;; bdd-fn-le-arg and of bdd-metric-is-metric-space.
;;;
;;; Helper prefix: bmb-.

;;; =====================================================================
;;; The kit.
;;; =====================================================================

;; 1-based index of FORM in the focus context, for `ineq'.
(define (bmb-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bmb-idx: not in context" form))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

;; `ineq' with the premises named by FORMULA rather than by position.
(define (bmb-ineq . forms) (apply ineq (map bmb-idx forms)))

;; `have!' HARDENED FOR REPEATED CLAIMS, which is what a forward block called
;; once per leaf produces.  Two things go wrong with the kit's `have!' here, and
;; both are the sequent hash-consing (dg-post! keys a node by its assertion plus
;; its context):
;;
;;  * the claim is ALREADY in context -- the cut self-loops and there is no main
;;    branch.  Declined outright.
;;  * the claim's SIDE GOAL is already GROUNDED.  Two sibling law leaves here
;;    (0 <= rho(u,v) and rho(u,v) = rho(v,u)) have the SAME context, so the
;;    second leaf's `(AND (IN 1 RR) (IN d(u,v) RR))' side goal is the node the
;;    first leaf already proved: `cut' opens only the main branch, `dk-opened'
;;    cannot see a grounded node, and `have!' dies with "no side goal" -- the
;;    trap trm-base! (theorem-library/trunc-metric-proof.scm) avoids by using
;;    `fact' instead of `have!'.  Here the side goal is simply SKIPPED when it
;;    comes back already proved, and the main branch is found by the claim being
;;    in ITS context rather than by elimination.
(define (bmb-have! f . opt)
  (if (find-first (lambda (g) (equal? g f)) (dk-asms))
      f
      (let* ((thunk (and (pair? opt) (car opt)))
             (new   (dk-opened (lambda () (cut f))))
             (side  (find-first (lambda (n) (alpha-equiv? (dk-goal-of n) f)) new))
             (main  (find-first (lambda (n)
                                  (and (not (eq? n side))
                                       (find-first (lambda (g) (equal? g f))
                                                   (dk-asms-of n))))
                                new)))
        (if side
            (begin (dk-focus! side)
                   (if thunk (thunk) (from-context!))
                   (if (not (sequent-node-grounded? side))
                       (error "bmb-have!: side goal left open" f))))
        (if (not main) (error "bmb-have!: no main branch for" f))
        (dk-focus! main)
        f)))

;; cut a ring identity (closed by `crs') and rewrite the goal with it.
(define (bmb-eq! e) (bmb-have! e (lambda () (crs))) (subst e))

(define (bmb-recip-of u) (list 'recip (list '+ 1 u)))
(define (bmb-quot-of u)  (list '* u (bmb-recip-of u)))          ; A(u)
(define (bmb-inv-of u)   (list '= (list '* (list '+ 1 u) (bmb-recip-of u)) 1))
(define (bmb-div-of u)   (list '/ u (list '+ 1 u)))             ; u/(1+u), as written

(define (bmb-mul! p q)
  (bmb-have! (list 'AND (list 'IN p 'RR) (list 'IN q 'RR)))
  (fact 'rr-mul-closed p q))

(define (bmb-nonneg! p q)
  (bmb-have! (list 'AND (list '<= 0 p) (list '<= 0 q)))
  (fact 'rr-leq-mul-nonneg p q))

;; 0, 1, and 0 < 1.
(define (bmb-base!)
  (fact 'rr-zero-in) (fact 'rr-one-in) (fact 'rr-zero-lt-one))

;; The reciprocal block for 1+u.  Needs (IN u RR) and (<= 0 u) in context.
(define (bmb-one-plus! u)
  (let ((den (list '+ 1 u)))
    (bmb-have! (list 'AND '(IN 1 RR) (list 'IN u 'RR)))
    (fact 'rr-add-closed 1 u)                       ; 1+u in RR
    (bmb-have! (list '<= 1 den) (lambda () (bmb-ineq (list '<= 0 u))))
    (bmb-have! (list 'AND '(< 0 1) (list '<= 1 den)))
    (fact 'rr-lt-le-trans 0 1 den)                  ; 0 < 1+u
    (fact 'rr-pos-ne-zero den)                      ; 1+u /= 0
    (bmb-have! (list 'AND (list 'IN den 'RR) (list 'NOT (list '= den 0))))
    (fact 'rr-recip-closed den)                     ; recip(1+u) in RR
    (fact 'rr-recip-inverse den)                    ; (1+u)*recip(1+u) = 1
    (fact 'rr-recip-pos den)                        ; 0 < recip(1+u)
    (bmb-have! (list '<= 0 den) (lambda () (bmb-ineq (list '<= 0 u))))
    (bmb-have! (list '<= 0 (bmb-recip-of u))
               (lambda () (bmb-ineq (list '< 0 (bmb-recip-of u)))))
    (bmb-mul! u (bmb-recip-of u))                   ; A(u) in RR
    (bmb-nonneg! u (bmb-recip-of u))))              ; 0 <= A(u)

;; recip(1+u) + A(u) = 1.
(define (bmb-inv-id! u)
  (let ((q (bmb-quot-of u)))
    (bmb-have! (list '= (list '+ (bmb-recip-of u) q) 1)
      (lambda ()
        (bmb-eq! (list '= (list '+ (bmb-recip-of u) q)
                       (list '* (list '+ 1 u) (bmb-recip-of u))))
        (ass)))))

;; A(u) + A(u)*u = u.
(define (bmb-quot-id! u)
  (let* ((q (bmb-quot-of u)) (qu (list '* q u)))
    (bmb-mul! q u)
    (bmb-have! (list '= (list '+ q qu) u)
      (lambda ()
        (bmb-eq! (list '= (list '+ q qu)
                       (list '* u (list '* (list '+ 1 u) (bmb-recip-of u)))))
        (subst (bmb-inv-of u))
        (crs)))))

;; Goal X <= Y, with (IN X RR), (IN Y RR), (IN C RR), 0 < C and X*C <= Y*C in
;; context: CLOSES it.
(define (bmb-cancel! x y c)
  (let ((d (list '- y x)))
    (bmb-have! (list 'AND (list 'IN y 'RR) (list 'IN x 'RR)))
    (fact 'rr-sub-in-rr y x)
    (bmb-mul! c d)
    (bmb-have! (list '= (list '* c d) (list '- (list '* y c) (list '* x c)))
               (lambda () (crs)))
    (bmb-have! (list '<= 0 (list '* c d))
      (lambda () (bmb-ineq (list '<= (list '* x c) (list '* y c))
                           (list '= (list '* c d)
                                 (list '- (list '* y c) (list '* x c))))))
    (fact 'rr-nonneg-cancel-pos c d)
    (bmb-ineq (list '<= 0 d))))

;;; =====================================================================
;;; L1.  bdd-fn-nonneg -- 0 <= t/(1+t).  `rr-leq-mul-nonneg' on the two
;;; factors, once the quotient is opened.
;;; =====================================================================

(sp (make-wff
     '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (<= 0 (/ t (+ 1 t))))))))
(dk-peel-to! '<=)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-one-plus! 't)
(ass)
(qed 'bdd-fn-nonneg)
;; (topic! 'bdd-fn-nonneg ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L2.  bdd-fn-lt-one -- t/(1+t) < 1.  From  recip(1+t) + A = 1  and
;;; 0 < recip(1+t): one Farkas step in the two atoms.
;;; =====================================================================

(sp (make-wff
     '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (< (/ t (+ 1 t)) 1))))))
(dk-peel-to! '<)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-one-plus! 't)
(bmb-inv-id! 't)
(bmb-ineq (list '= (list '+ (bmb-recip-of 't) (bmb-quot-of 't)) 1)
          (list '< 0 (bmb-recip-of 't)))
(qed 'bdd-fn-lt-one)
;; (topic! 'bdd-fn-lt-one ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L3.  bdd-fn-le-arg -- t/(1+t) <= t.  From  A + A*t = t  and 0 <= A*t.
;;; =====================================================================

(sp (make-wff
     '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t) (<= (/ t (+ 1 t)) t))))))
(dk-peel-to! '<=)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-one-plus! 't)
(bmb-quot-id! 't)
(bmb-nonneg! (bmb-quot-of 't) 't)
(bmb-ineq (list '<= 0 (list '* (bmb-quot-of 't) 't))
          (list '= (list '+ (bmb-quot-of 't) (list '* (bmb-quot-of 't) 't)) 't))
(qed 'bdd-fn-le-arg)
;; (topic! 'bdd-fn-le-arg ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L4.  bdd-fn-zero -- t = 0 gives t/(1+t) = 0.  A and A*t are nonnegative
;;; and sum to t.
;;; =====================================================================

(sp (make-wff
     '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t)
        (IMPLIES (= t 0) (= (/ t (+ 1 t)) 0)))))))
(dk-peel-to! '=)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-one-plus! 't)
(bmb-quot-id! 't)
(bmb-nonneg! (bmb-quot-of 't) 't)
(bmb-ineq (list '= (list '+ (bmb-quot-of 't) (list '* (bmb-quot-of 't) 't)) 't)
          '(= t 0)
          (list '<= 0 (bmb-quot-of 't))
          (list '<= 0 (list '* (bmb-quot-of 't) 't)))
(qed 'bdd-fn-zero)
(topic! 'bdd-fn-zero 'inequalities)

;;; =====================================================================
;;; L5.  bdd-fn-zero-eq -- the CONVERSE, and the "missing scalar lemma" the
;;; triage recorded as the obstacle under bdd-metric-is-metric-space.  A = 0
;;; forces A*t = 0, and A + A*t = t then reads t = 0.
;;; =====================================================================

(sp (make-wff
     '(FORALL t (IMPLIES (IN t RR) (IMPLIES (<= 0 t)
        (IMPLIES (= (/ t (+ 1 t)) 0) (= t 0)))))))
(dk-peel-to! '=)
(mac-h 'binary-divide-def '(= (/ t (+ 1 t)) 0))
(bmb-base!)
(bmb-one-plus! 't)
(bmb-quot-id! 't)
(bmb-have! (list '= (list '* (bmb-quot-of 't) 't) 0)
  (lambda () (subst (list '= (bmb-quot-of 't) 0)) (crs)))
(bmb-ineq (list '= (list '+ (bmb-quot-of 't) (list '* (bmb-quot-of 't) 't)) 't)
          (list '= (bmb-quot-of 't) 0)
          (list '= (list '* (bmb-quot-of 't) 't) 0))
(qed 'bdd-fn-zero-eq)
(topic! 'bdd-fn-zero-eq 'inequalities)

;;; =====================================================================
;;; L6.  bdd-fn-mono -- f is increasing.  Clear (1+s)(1+t) and the goal is
;;; s + s*t <= t + s*t.
;;; =====================================================================

(sp (make-wff '(FORALL s (IMPLIES (IN s RR) (FORALL t (IMPLIES (IN t RR)
     (IMPLIES (AND (<= 0 s) (<= s t))
              (<= (/ s (+ 1 s)) (/ t (+ 1 t))))))))))
(dk-peel-to! '<=)
(dk-split-all!)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-have! '(<= 0 t) (lambda () (bmb-ineq '(<= 0 s) '(<= s t))))
(bmb-one-plus! 's)
(bmb-one-plus! 't)
(define mo-qs (bmb-quot-of 's))
(define mo-qt (bmb-quot-of 't))
(define mo-c '(* (+ 1 s) (+ 1 t)))
(bmb-mul! '(+ 1 s) '(+ 1 t))                       ; c in RR
(bmb-have! '(AND (< 0 (+ 1 s)) (< 0 (+ 1 t))))
(fact 'rr-mul-pos '(+ 1 s) '(+ 1 t))               ; 0 < c
(bmb-mul! mo-qs mo-c)
(bmb-mul! mo-qt mo-c)
(bmb-mul! 's 't)
(bmb-nonneg! 's 't)                                ; 0 <= s*t
(bmb-have! (list '= (list '* mo-qs mo-c) '(+ s (* s t)))
  (lambda ()
    (bmb-eq! (list '= (list '* mo-qs mo-c)
                   (list '* '(+ s (* s t)) (list '* '(+ 1 s) (bmb-recip-of 's)))))
    (subst (bmb-inv-of 's))
    (crs)))
(bmb-have! (list '= (list '* mo-qt mo-c) '(+ t (* s t)))
  (lambda ()
    (bmb-eq! (list '= (list '* mo-qt mo-c)
                   (list '* '(+ t (* s t)) (list '* '(+ 1 t) (bmb-recip-of 't)))))
    (subst (bmb-inv-of 't))
    (crs)))
(bmb-have! (list '<= (list '* mo-qs mo-c) (list '* mo-qt mo-c))
  (lambda () (bmb-ineq (list '= (list '* mo-qs mo-c) '(+ s (* s t)))
                       (list '= (list '* mo-qt mo-c) '(+ t (* s t)))
                       '(<= s t))))
(bmb-cancel! mo-qs mo-qt mo-c)
(qed 'bdd-fn-mono)
;; (topic! 'bdd-fn-mono ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L7.  bdd-fn-subadd -- THE key fact.  Clear (1+a+b)(1+a)(1+b) and the
;;; difference is  2ab + a^2 b + a b^2, three products of nonnegatives.
;;; =====================================================================

(define sa-s '(+ a b))
(define sa-ra (bmb-recip-of 'a))
(define sa-rb (bmb-recip-of 'b))
(define sa-rs (bmb-recip-of sa-s))
(define sa-x (list '* sa-s sa-rs))
(define sa-y (list '+ (list '* 'a sa-ra) (list '* 'b sa-rb)))
(define sa-ab '(* (+ 1 a) (+ 1 b)))
(define sa-c (list '* (list '+ 1 sa-s) sa-ab))
(define sa-p (list '* sa-s sa-ab))
(define sa-q1 (list '* 'a (list '* (list '+ 1 sa-s) '(+ 1 b))))
(define sa-q2 (list '* 'b (list '* (list '+ 1 sa-s) '(+ 1 a))))
(define sa-q (list '+ sa-q1 sa-q2))
(define sa-diff '(+ (+ (* 2 (* a b)) (* (* a b) a)) (* (* a b) b)))

(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (IMPLIES (AND (<= 0 a) (<= 0 b))
       (<= (/ (+ a b) (+ 1 (+ a b)))
           (+ (/ a (+ 1 a)) (/ b (+ 1 b)))))))))))
(dk-peel-to! '<=)
(dk-split-all!)
(mac 'binary-divide-def)
(bmb-base!)
(bmb-have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
(bmb-have! (list '<= 0 sa-s) (lambda () (bmb-ineq '(<= 0 a) '(<= 0 b))))
(bmb-one-plus! 'a)
(bmb-one-plus! 'b)
(bmb-one-plus! sa-s)
(bmb-have! (list 'AND (list 'IN (list '* 'a sa-ra) 'RR)
                 (list 'IN (list '* 'b sa-rb) 'RR)))
(fact 'rr-add-closed (list '* 'a sa-ra) (list '* 'b sa-rb))    ; Y in RR
(bmb-mul! '(+ 1 a) '(+ 1 b))
(bmb-mul! (list '+ 1 sa-s) sa-ab)                              ; c in RR
(bmb-have! '(AND (< 0 (+ 1 a)) (< 0 (+ 1 b))))
(fact 'rr-mul-pos '(+ 1 a) '(+ 1 b))
(bmb-have! (list 'AND (list '< 0 (list '+ 1 sa-s)) (list '< 0 sa-ab)))
(fact 'rr-mul-pos (list '+ 1 sa-s) sa-ab)                      ; 0 < c
(bmb-mul! sa-s sa-ab)                                          ; P
(bmb-mul! (list '+ 1 sa-s) '(+ 1 b))
(bmb-mul! 'a (list '* (list '+ 1 sa-s) '(+ 1 b)))              ; Q1
(bmb-mul! (list '+ 1 sa-s) '(+ 1 a))
(bmb-mul! 'b (list '* (list '+ 1 sa-s) '(+ 1 a)))              ; Q2
(bmb-mul! sa-x sa-c)
(bmb-mul! sa-y sa-c)
(bmb-mul! 'a 'b)
(bmb-nonneg! 'a 'b)
(bmb-mul! '(* a b) 'a)
(bmb-nonneg! '(* a b) 'a)
(bmb-mul! '(* a b) 'b)
(bmb-nonneg! '(* a b) 'b)
(bmb-have! (list '= (list '* sa-x sa-c) sa-p)
  (lambda ()
    (bmb-eq! (list '= (list '* sa-x sa-c)
                   (list '* sa-p (list '* (list '+ 1 sa-s) sa-rs))))
    (subst (bmb-inv-of sa-s))
    (crs)))
(bmb-have! (list '= (list '* sa-y sa-c) sa-q)
  (lambda ()
    (bmb-eq! (list '= (list '* sa-y sa-c)
                   (list '+ (list '* sa-q1 (list '* '(+ 1 a) sa-ra))
                            (list '* sa-q2 (list '* '(+ 1 b) sa-rb)))))
    (subst (bmb-inv-of 'a))
    (subst (bmb-inv-of 'b))
    (crs)))
(bmb-have! (list '= (list '- sa-q sa-p) sa-diff) (lambda () (crs)))
(bmb-have! (list '<= sa-p sa-q)
  (lambda () (bmb-ineq (list '= (list '- sa-q sa-p) sa-diff)
                       '(<= 0 (* a b))
                       '(<= 0 (* (* a b) a))
                       '(<= 0 (* (* a b) b)))))
(bmb-have! (list '<= (list '* sa-x sa-c) (list '* sa-y sa-c))
  (lambda () (bmb-ineq (list '= (list '* sa-x sa-c) sa-p)
                       (list '= (list '* sa-y sa-c) sa-q)
                       (list '<= sa-p sa-q))))
(bmb-cancel! sa-x sa-y sa-c)
(qed 'bdd-fn-subadd)
;; (topic! 'bdd-fn-subadd ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L8.  bdd-metric-bounded -- every rho-distance is < 1.
;;; =====================================================================

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (< ((DIST (BDD-METRIC s)) x y) 1)))))))))
(dk-peel-to! '<)
(fact 'metric-dist-real 's 'x 'y)
(fact 'metric-pos 's 'x 'y)
(fact 'bdd-metric-distance 's 'x 'y)
(subst '(= ((DIST (BDD-METRIC s)) x y)
           (/ ((DIST s) x y) (+ 1 ((DIST s) x y)))))
(fact 'bdd-fn-lt-one '((DIST s) x y))
(ass)
(qed 'bdd-metric-bounded)
;; (topic! 'bdd-metric-bounded ...) is already filed in theorem-library/pss-topics.scm

;;; =====================================================================
;;; L9.  bdd-metric-is-metric-space.
;;; =====================================================================

(define (bmb-dd u v) (list (list 'DIST 's) u v))            ; d(u,v)
(define (bmb-rho u v) (list (list 'DIST '(BDD-METRIC s)) u v))

;; d(u,v) in RR, 0 <= d(u,v), the reciprocal block, and f(d) in RR.
(define (bmb-pair-core! u v)
  (let ((d (bmb-dd u v)))
    (fact 'metric-dist-real 's u v)
    (fact 'metric-pos 's u v)
    (bmb-one-plus! d)
    d))

;; ... and the quotient typing on top.  NOT usable where (IN f(d) RR) IS the
;; focus goal: cutting a claim equal to the goal is an alpha self-loop with no
;; main branch (CLAUDE.md).  The lam-t pointwise leaf is exactly that case and
;; calls the core plus `mac' + `ass' instead.
(define (bmb-pair! u v)
  (let ((d (bmb-pair-core! u v)))
    (bmb-have! (list 'IN (bmb-div-of d) 'RR)
               (lambda () (mac 'binary-divide-def) (ass)))
    d))

;; rewrite rho(u,v) into d(u,v)/(1+d(u,v)) in the GOAL.
(define (bmb-open-rho! u v)
  (fact 'bdd-metric-distance 's u v)
  (subst (list '= (bmb-rho u v) (bmb-div-of (bmb-dd u v)))))

;; `di' every open leaf whose goal is a FORALL/IMPLIES/AND, to exhaustion.
(define (bmb-drive!)
  (let loop ((fuel 60))
    (let ((n (find-first (lambda (n)
                           (let ((g (dk-goal-of n)))
                             (and (not (sequent-node-grounded? n))
                                  (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
                         (proof-leaves))))
      (if (and n (> fuel 0)) (begin (dk-focus! n) (di) (loop (- fuel 1))) #t))))

;; split the focus AND goal all the way down; return the atom leaves.
(define (bmb-split-goal!)
  (let walk ((n (proof-state-focus *ps*)) (acc '()))
    (dk-focus! n)
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'AND))
          (let loop ((ks (dk-opened (lambda () (di)))) (acc acc))
            (if (null? ks) acc (loop (cdr ks) (walk (car ks) acc))))
          (cons n acc)))))

;; (IN (PTS s) SET), off the folded hypothesis.  `mac-h' is destructive, but
;; each leaf is its own sequent node, so the siblings keep IS-METRIC-SPACE(s).
(define (bmb-pts-set!)
  (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s))
  (dk-split-all!)
  (ass))

;; the five metric laws for rho, dispatched on the shape of the leaf.
(define (bmb-law!)
  (let ((g (dk-goal)))
    (cond
      ;; rho(u,u) = 0
      ((and (eq? (car g) '=) (equal? (caddr g) 0))
       (let* ((u (cadr (cadr g))))
         (bmb-base!) (bmb-pair! u u)
         (bmb-open-rho! u u)
         (fact 'metric-self-zero 's u)
         (fact 'bdd-fn-zero (bmb-dd u u))
         (ass)))
      ;; 0 <= rho(u,v)
      ((and (eq? (car g) '<=) (equal? (cadr g) 0))
       (let* ((r (caddr g)) (u (cadr r)) (v (caddr r)))
         (bmb-base!) (bmb-pair! u v)
         (bmb-open-rho! u v)
         (fact 'bdd-fn-nonneg (bmb-dd u v))
         (ass)))
      ;; rho(u,v) = 0  |-  u = v
      ((and (eq? (car g) '=) (symbol? (cadr g)) (symbol? (caddr g)))
       (let* ((u (cadr g)) (v (caddr g))
              (d (bmb-dd u v)) (fd (bmb-div-of d)))
         (bmb-base!) (bmb-pair! u v)
         (fact 'bdd-metric-distance 's u v)
         (bmb-have! (list '= fd (bmb-rho u v))
           (lambda () (subst (list '= (bmb-rho u v) fd)) (rfl)))
         (bmb-have! (list '= fd 0)
           (lambda () (subst (list '= fd (bmb-rho u v))) (ass)))
         (fact 'bdd-fn-zero-eq d)
         (fact 'metric-zero-eq 's u v)
         (ass)))
      ;; rho(u,v) = rho(v,u)
      ((eq? (car g) '=)
       (let* ((u (cadr (cadr g))) (v (caddr (cadr g))))
         (bmb-base!) (bmb-pair! u v) (bmb-pair! v u)
         (bmb-open-rho! u v)
         (bmb-open-rho! v u)
         (fact 'metric-sym 's u v)
         (subst (list '= (bmb-dd u v) (bmb-dd v u)))
         (rfl)))
      ;; rho(u,w) <= rho(u,v) + rho(v,w)
      ((eq? (car g) '<=)
       (let* ((lhs (cadr g)) (rhs (caddr g))
              (u (cadr lhs)) (w (caddr lhs))
              (v (caddr (cadr rhs)))
              (duw (bmb-dd u w)) (duv (bmb-dd u v)) (dvw (bmb-dd v w))
              (sum (list '+ duv dvw)))
         (bmb-base!)
         (bmb-pair! u w) (bmb-pair! u v) (bmb-pair! v w)
         (bmb-open-rho! u w)
         (bmb-open-rho! u v)
         (bmb-open-rho! v w)
         (fact 'metric-triangle 's u v w)
         (bmb-have! (list 'AND (list 'IN duv 'RR) (list 'IN dvw 'RR)))
         (fact 'rr-add-closed duv dvw)
         (bmb-have! (list '<= 0 sum)
                    (lambda () (bmb-ineq (list '<= 0 duv) (list '<= 0 dvw))))
         (bmb-one-plus! sum)
         (bmb-have! (list 'IN (bmb-div-of sum) 'RR)
                    (lambda () (mac 'binary-divide-def) (ass)))
         ;; both have a CONJUNCTIVE antecedent, which `fact' will not split:
         ;; without the `have!' the citation lands the IMPLICATION, silently.
         (bmb-have! (list 'AND (list '<= 0 duw) (list '<= duw sum)))
         (fact 'bdd-fn-mono duw sum)
         (bmb-have! (list 'AND (list '<= 0 duv) (list '<= 0 dvw)))
         (fact 'bdd-fn-subadd duv dvw)
         (bmb-ineq (list '<= (bmb-div-of duw) (bmb-div-of sum))
                   (list '<= (bmb-div-of sum)
                         (list '+ (bmb-div-of duv) (bmb-div-of dvw))))))
      (#t (error "bmb-law!: unexpected leaf" g)))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
                 (IS-METRIC-SPACE (BDD-METRIC s))))))
(di) (di)
(mac 'IS-METRIC-SPACE)                       ; the GOAL only
(mac 'bdd-metric-carrier)                    ; PTS(BDD-METRIC s) -> PTS(s)
(define bmb-conjuncts (bmb-split-goal!))

;; everything but `is-metric', which is left for last so bmb-drive! sees only
;; its own descendants.
(for-each
 (lambda (n)
   (if (not (sequent-node-grounded? n))
       (begin
         (dk-focus! n)
         (let ((g (dk-goal)))
           (cond
             ;; length(BDD-METRIC s) = 2
             ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
              (mac 'BDD-METRIC) (len-r) (arith))
             ;; PTS(s) in SET
             ((equal? g '(IN (PTS s) SET)) (bmb-pts-set!))
             ;; DIST(BDD-METRIC s) in FUN(PTS x PTS, RR)
             ((eq? (car g) 'IN)
              (mac 'BDD-METRIC) (slot 'DIST) (nth-r)
              (for-each
               (lambda (k)
                 (dk-focus! k)
                 (let ((gg (dk-goal)))
                   (cond
                     ;; the SETHOOD leaf lam-t always owes
                     ((and (eq? (car gg) 'IN) (eq? (caddr gg) 'SET))
                      (mac 'cartesian-set-iff)
                      (for-each (lambda (j)
                                  (if (not (sequent-node-grounded? j))
                                      (begin (dk-focus! j) (bmb-pts-set!))))
                                (dk-opened (lambda () (di)))))
                     ;; the pointwise typing of the body
                     (#t
                      (dk-peel!)
                      (let* ((d (cadr (cadr (dk-goal))))
                             (u (cadr d)) (v (caddr d)))
                        (bmb-base!) (bmb-pair-core! u v)
                        (mac 'binary-divide-def) (ass))))))
               (dk-opened (lambda () (lam-t)))))
             (#t 'is-metric-later))))))
 bmb-conjuncts)

;; now the metric laws.
(dk-focus-goal! "is-metric(")
(mac 'is-metric)
(bmb-drive!)
(for-each (lambda (n)
            (if (not (sequent-node-grounded? n))
                (begin (dk-focus! n) (bmb-law!))))
          (proof-leaves))
(qed 'bdd-metric-is-metric-space)
;; (topic! 'bdd-metric-is-metric-space ...) is already filed in theorem-library/pss-topics.scm
