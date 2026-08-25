;;; continuity-local.scm -- CONTINUITY AT A POINT READS ONLY A NEIGHBOURHOOD OF
;;; IT: a map agreeing with a continuous map on a BALL about the point, and
;;; saying nothing whatever elsewhere, is continuous at that point.  PROVEN.
;;;
;;;   f in FUN(RR,RR),  0 < rho,  g continuous at t,
;;;   f(x) = g(x) whenever |x - t| <= rho        =>   f continuous at t
;;;
;;; THE LOCAL TWIN OF cont-transfer-ptwise-eq, and it stands to that theorem
;;; exactly as `diff-at-local' (theorem-library/diff-at-local.scm) stands to
;;; the global Caratheodory identity.  `cont-transfer-ptwise-eq'
;;; (continuity-transfer.scm) asks for agreement at EVERY real, which is what a
;;; function BUILT on an interval cannot supply: the calculus arc's habit is to
;;; construct a map by a limit or a description that is meaningful on [a,b] and
;;; junk outside it, and a transfer demanding global agreement cannot be cited
;;; about it at all.  Locality is carried by a radius, as everywhere else in
;;; this corner of the tree (uniform-limit-local.scm, diff-at-local.scm), so
;;; that no metric subspace structure on CCINT(a,b) is needed or implied.
;;;
;;; THE PROOF is continuity-transfer's with ONE change: the delta handed back
;;; is capped, `rr-min-pos' on g's own delta_0 and rho, so that every point the
;;; eps/delta clause looks at lies in the ball where the agreement hypothesis
;;; speaks.  The estimate is otherwise untouched -- the two distances are not
;;; merely close, they are the same number -- so there is no epsilon
;;; arithmetic, and `ineq' is used only to move `<=' along the cap.
;;;
;;; The agreement is needed at the CENTRE too, which costs the one-line
;;; |t - t| = 0 <= rho; and the DIST reading of the ball has to be taken on a
;;; `have!' lane, `mac-h' being destructive and the DIST form being what g's
;;; delta-universal is instantiated against.
;;;
;;; The two IS-METRIC-SPACE conjuncts of the goal come out of g's own unfold
;;; and are never cited, which is what keeps the bill at zero: citing
;;; `rr-is-metric-space' (still an asserted support) would put it in this bill
;;; and in every bill downstream.  `modulo 0'.
;;;
;;; Loads after metric-continuity (IS-CONTINUOUS-AT), rr-metric-space, rr-ms-dist,
;;; rr-order-basics (rr-min-pos, rr-le-ne-lt, rr-lt-implies-le, rr-leq-reflexive),
;;; rr-abs-basics (rr-abs-closed, rr-abs-sub-sym, rr-abs-of-nonneg),
;;; binary-minus-laws (rr-sub-in-rr) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `cl-' prefix) --------------------

(define (cl-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (cl-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cl-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands -- never a `di' count.
(define (cl-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cl-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (cl-di-landed-1!)
  (let ((new (cl-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "cl-di-landed-1!: expected 1" (map expression->string new)))))

(define (cl-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cl-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cl-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

;;; skolemize a FORSOME already in the CONTEXT; returns (LANDED . (EIGENVARS)).
(define (cl-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (cl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cl-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (cl-ineq . forms) (apply ineq (map cl-idx forms)))

;;; POS-RR(d) opened into the strict form `rr-min-pos' guards on.  DESTRUCTIVE:
;;; every use of the folded predicate must already have happened.
(define (cl-pos->lt! d)
  (mac-h 'pos-rr (list 'POS-RR d))
  (dk-split! (list 'AND (list 'IN d 'RR)
                   (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d)))))
  (have! (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))
  (fact 'rr-le-ne-lt 0 d))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff "forall([f in fun(rr,rr), g in fun(rr,rr), t_ in rr, rho in rr],
   0 < rho implies
   is-continuous-at(rr-ms, rr-ms, g, t_) implies
   forall([x_ in rr], abs(x_ - t_) <= rho implies f(x_) = g(x_)) implies
   is-continuous-at(rr-ms, rr-ms, f, t_))"))
(quietly (lambda () (cl-peel!)))
(define CL-PW (car (dk-asms)))          ; the LOCAL pointwise equality
(define CL-CG (cadr (dk-asms)))         ; g is continuous at t_

(quietly (lambda ()
  (fact 'rr-zero-in)
  (fact 'rr-lt-implies-le 0 'rho)
  (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at CL-CG))))))

(define CL-EPSU
  (cl-find 'eps (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                 (dk-contains? a 'POS-RR) (dk-contains? a 'DIST)))))

;;; The b-branch.  b is within dl of t_, hence within rho, so the agreement
;;; hypothesis speaks at b; it speaks at t_ because |t_ - t_| = 0 <= rho.  The
;;; two `subst's then turn the goal into g's own conclusion.
(define (cl-inner! del dl du2)
  (let* ((mb (cl-di-landed-1!)) (b (cadr mb)))
    (have! (list 'IN b 'RR)
      (lambda () (slot-h 'PTS (list 'IN b '(PTS RR-MS))) (ass)))
    (let ((dstb (car (cl-di-landed!))))
      (fact 'rr-sub-in-rr 't_ b)
      (fact 'rr-abs-closed (list '- 't_ b))
      (fact 'rr-sub-in-rr b 't_)
      (fact 'rr-abs-closed (list '- b 't_))
      ;; the abs reading of d(t_,b) <= dl, on a LANE: the DIST form is what g's
      ;; delta-universal is instantiated against, and `mac-h' would delete it.
      (have! (list '<= (list 'abs (list '- 't_ b)) dl)
        (lambda () (mac-h 'rr-ms-dist dstb) (ass)))
      (have! (list '<= (list '(DIST RR-MS) 't_ b) del)
        (lambda () (mac 'rr-ms-dist)
                   (cl-ineq (list '<= (list 'abs (list '- 't_ b)) dl)
                            (list '<= dl del))))
      (cl-inst! du2 b)                     ; d(g(t_), g(b)) <= eps
      (fact 'rr-abs-sub-sym 't_ b)
      (have! (list '<= (list 'abs (list '- b 't_)) 'rho)
        (lambda () (cl-ineq (list '= (list 'abs (list '- 't_ b))
                                     (list 'abs (list '- b 't_)))
                            (list '<= (list 'abs (list '- 't_ b)) dl)
                            (list '<= dl 'rho))))
      (have! (list '<= (list 'abs '(- t_ t_)) 'rho)
        (lambda ()
          (have! '(= (- t_ t_) 0) (lambda () (crs)))
          (subst '(= (- t_ t_) 0))
          (fact 'rr-leq-reflexive 0)
          (fact 'rr-abs-of-nonneg 0)
          (subst '(= (abs 0) 0))
          (ass)))
      (cl-inst! CL-PW 't_)
      (cl-inst! CL-PW b)
      (subst (list '= (list 'f 't_) (list 'g 't_)))
      (subst (list '= (list 'f b) (list 'g b)))
      (ass))))

;;; The eps branch: g's own delta_0, CAPPED at rho.  `rr-min-pos' states the cap
;;; existentially, so no MIN term enters the proof.
(define (cl-eps!)
  (let* ((me (cl-di-landed-1!)) (eps (cadr me)))
    (let* ((sk (cl-skolem! (cl-inst! CL-EPSU eps)))
           (del (car (cadr sk))))
      (dk-split! (car sk))
      (let ((du2 (cl-find 'inner
                   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                    (dk-contains? a del)
                                    (dk-contains? a 'DIST))))))
        (cl-pos->lt! del)
        (let* ((mp (cl-skolem! (dk-fact! 'rr-min-pos del 'rho)))
               (dl (car (cadr mp))))
          (dk-split! (car mp))
          (mac-h '< (list '< 0 dl))
          (dk-split! (list 'AND (list '<= 0 dl) (list 'NOT (list '= 0 dl))))
          (ew dl)
          (cl-and!
           (lambda ()
             (if (eq? (car (dk-goal)) 'POS-RR)
                 (begin (mac 'pos-rr) (from-context!))
                 (cl-inner! del dl du2)))))))))

(quietly (lambda ()
  (mac 'is-continuous-at)
  (cl-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
             ((and (eq? (car gl) 'IN) (dk-contains? gl 'PTS)) (slot 'PTS) (ass))
             (else (cl-eps!))))))))
(qed 'continuous-at-local)
(topic! 'continuous-at-local 'analysis)
(alias! 'continuous-at-local
        "continuity at a point is a local property"
        "a map agreeing with a continuous map near a point is continuous there")
