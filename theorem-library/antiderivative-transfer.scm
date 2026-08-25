;;; antiderivative-transfer.scm -- the POINTWISE TRANSFER for Def 4.6, and the
;;; DIFFERENCE of two antiderivatives.  All three `modulo 0'.
;;;
;;;   antiderivative-transfer-ptwise-eq
;;;       f, psi in FUN(RR,RR),  IS-ANTIDERIVATIVE(g, phi, a, b),
;;;       f = g pointwise,  psi = phi pointwise   =>  IS-ANTIDERIVATIVE(f, psi, a, b)
;;;
;;;   antiderivative-sub    Prop 4.8's third case: F - G is an antiderivative of
;;;                         phi - psi on [a,b]
;;;   antiderivable-sub     ... and the same one storey up
;;;
;;; WHY THE TRANSFER.  It is the joint the continuity algebra needed and got in
;;; `cont-transfer-ptwise-eq' (continuity-transfer.scm), and the differentiation
;;; arc got in `diff-transfer-ptwise-eq' (diff-transfer.scm), one predicate up.
;;; Def 4.6 is a conjunction of a continuity clause and a derivative clause, so
;;; the two existing transfers ARE the proof -- there is no new mathematics here
;;; at all, only the observation that the transfer is available for
;;; IS-ANTIDERIVATIVE the moment it is available for both conjuncts.  Without it
;;; every theorem about antiderivatives concludes about the LITERAL lambda the
;;; theorem built, and a proof holding some other term that happens to agree
;;; with it pointwise cannot cite it.  This is exactly the obstacle
;;; continuity-transfer.scm's header describes, met one level up.
;;;
;;; TWO SLOTS, NOT ONE, and that is the point.  A composition of Prop 4.8's
;;; halves -- scale by -1, then add -- rewrites BOTH arguments of the predicate:
;;; the conclusion is about the antiderivative `x |-> f(x) + (VNB-LAMBDA ...)(x)'
;;; AND about the function `x |-> phi(x) + (VNB-LAMBDA ...)(x)'.  A transfer
;;; that moved only the antiderivative slot would leave the second unusable.
;;;
;;; THE ONE MECHANICAL POINT.  The hypotheses are stated with STRICT `=' -- the
;;; form `crs' proves, hence the form a citer will have -- while
;;; `diff-transfer-ptwise-eq' asks for the QUASI-equality `=='.  The bridge is
;;; four lines at the head of the proof: peel the universal, instantiate the `='
;;; form, `subst' it into the `==' goal and close X == X with `qrfl'.
;;; `cont-transfer-ptwise-eq' wants `=' and takes the hypothesis unchanged.
;;;
;;; A NOTE ON antiderivative-sub, because the obvious route is the wrong one.
;;; It is NOT proved through the transfer.  Composing antiderivative-scale at
;;; c = -1 with antiderivative-add reaches `x |-> f(x) + (-1).g(x)' and then
;;; needs the transfer to cross to `x |-> f(x) - g(x)'.  That works, and it is
;;; three citations where one driver does: `sub-lam-in-fun' and
;;; `sub-continuous-at' (continuity-sub.scm) and `deriv-sub'
;;; (antiderivative.scm) are all proven and all have exactly the shapes
;;; antiderivative-add's driver consumes, so the difference is that driver with
;;; three names changed.  The transfer is proved here anyway, on its own merits:
;;; it is the general-purpose half, and the MVT estimate of Prop 4.16 is not the
;;; only thing that will want it.
;;;
;;; Loads immediately after antiderivative (IS-ANTIDERIVATIVE, IS-ANTIDERIVABLE,
;;; deriv-sub), and needs continuity-transfer (cont-transfer-ptwise-eq),
;;; diff-transfer (diff-transfer-ptwise-eq), continuity-sub (sub-lam-in-fun,
;;; sub-continuous-at), fun-apply-type-proof and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `at-' prefix) --------------------

;; peel a guarded universal, returning the eigenvariable of the guard it landed
(define (at-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; `di' splits a conjunctive GOAL one level per call; split every AND leaf.
(define (at-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;; a context universal, taken on the head of its CONSEQUENT plus the map it
;; speaks about -- never by position: the four in `antiderivative-sub' below are
;; two shapes twice over.
(define (at-univ head sym)
  (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                (dk-contains? z head) (dk-contains? z sym)))
               (dk-asms))))

;;; =====================================================================
;;; 1.  THE POINTWISE TRANSFER.
;;; =====================================================================

(quietly (lambda ()
 (sp (make-wff "forall([f in fun(rr,rr), psi in fun(rr,rr)],
   forall([g, phi, a, b],
     is-antiderivative(g, phi, a, b) implies
     forall([x_ in rr], f(x_) = g(x_)) implies
     forall([x_ in rr], psi(x_) = phi(x_)) implies
     is-antiderivative(f, psi, a, b)))"))
 (dk-peel-to! 'IS-ANTIDERIVATIVE)))
(define AT-PWP (car (dk-asms)))          ; psi = phi pointwise
(define AT-PWF (cadr (dk-asms)))         ; f   = g   pointwise

(quietly (lambda ()
  ;; the QUASI-equality form of AT-PWF, which diff-transfer-ptwise-eq asks for.
  (have! '(FORALL x_ (IMPLIES (IN x_ RR) (== (f x_) (g x_))))
    (lambda ()
      (di)
      (let* ((gl (dk-goal)) (v (cadr (cadr gl))))
        (dk-deepest (lambda () (inst+ AT-PWF v)))
        (subst (list '= (list 'f v) (list 'g v)))
        (qrfl))))
  (dk-split! (dk-landed-1
    (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE g phi a b)))))))
(define at-cg (at-univ 'IS-CONTINUOUS-AT 'g))
(define at-dg (at-univ 'IS-DIFF-AT 'phi))

(quietly (lambda ()
  (mac 'IS-ANTIDERIVATIVE)
  (at-split-goal!)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (let ((gl (dk-goal)))
       (cond
         ((memq (car gl) '(IN <)) (ass))
         ((eq? (car (cadr (caddr gl))) 'IN)                ; continuity clause
          (let ((v (at-di-var!)))
            (inst+ at-cg v)
            (fact 'cont-transfer-ptwise-eq 'f 'g v)
            (ass)))
         (else                                             ; derivative clause
          (di)
          (dk-split! (dk-landed-1 (lambda () (di))))
          (let ((v (caddr (dk-goal))))
            (have! (list 'AND (list 'IN v 'RR)
                              (list 'AND (list '< 'a v) (list '< v 'b))))
            (inst+ at-dg v)
            (fact 'diff-transfer-ptwise-eq 'f 'g v (list 'phi v))
            (dk-deepest (lambda () (inst+ AT-PWP v)))
            (subst (list '= (list 'psi v) (list 'phi v)))
            (ass))))))
   (proof-leaves))))
(qed 'antiderivative-transfer-ptwise-eq)
(topic! 'antiderivative-transfer-ptwise-eq 'analysis)
(alias! 'antiderivative-transfer-ptwise-eq
        "an antiderivative is one of any function agreeing with it pointwise")

;;; =====================================================================
;;; 2.  PROPOSITION 4.8, the DIFFERENCE.  antiderivative-add's driver with
;;; `sub-' for `sum-' and `deriv-sub' for `deriv-sum'.
;;; =====================================================================

(define at-sub-f   '(VNB-LAMBDA x RR (- (f x) (g x))))
(define at-sub-phi '(VNB-LAMBDA x RR (- (phi x) (psi x))))

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'phi (list 'FORALL 'psi
      (list 'FORALL 'a (list 'FORALL 'b
        (list 'IMPLIES '(IS-ANTIDERIVATIVE f phi a b)
        (list 'IMPLIES '(IS-ANTIDERIVATIVE g psi a b)
          (list 'IS-ANTIDERIVATIVE at-sub-f at-sub-phi 'a 'b)))))))))))
  (dk-peel-to! 'IS-ANTIDERIVATIVE)
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b)))))
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE g psi a b)))))
  (let ((sb-cf (at-univ 'IS-CONTINUOUS-AT 'f))
        (sb-df (at-univ 'IS-DIFF-AT 'phi))
        (sb-cg (at-univ 'IS-CONTINUOUS-AT 'g))
        (sb-dg (at-univ 'IS-DIFF-AT 'psi)))
    (fact 'sub-lam-in-fun 'f 'g)
    (fact 'sub-lam-in-fun 'phi 'psi)
    (mac 'IS-ANTIDERIVATIVE)
    (at-split-goal!)
    (for-each
     (lambda (nd)
       (dk-focus! nd)
       (let ((gl (dk-goal)))
         (cond
           ((memq (car gl) '(IN <)) (ass))
           ((eq? (car (cadr (caddr gl))) 'IN)              ; continuity clause
            (let ((v (at-di-var!)))
              (inst+ sb-cf v) (inst+ sb-cg v)
              (fact 'sub-continuous-at 'f 'g v)
              (ass)))
           (else                                          ; derivative clause
            (di)
            (dk-split! (dk-landed-1 (lambda () (di))))
            (let ((v (caddr (dk-goal))))
              (have! (list 'AND (list 'IN v 'RR)
                                (list 'AND (list '< 'a v) (list '< v 'b))))
              (inst+ sb-df v) (inst+ sb-dg v)
              ;; th TYPED before the beta, or `lam-b' owes an (IN th RR) at a
              ;; node where th does not occur
              (fact 'fun-apply-type-c 'phi 'RR 'RR v)
              (fact 'fun-apply-type-c 'psi 'RR 'RR v)
              (lam-b)                                     ; PHI(th) -> phi(th)-psi(th)
              (have! (list 'AND (list 'IS-DIFF-AT 'f v (list 'phi v))
                                (list 'IS-DIFF-AT 'g v (list 'psi v))))
              (fact 'deriv-sub 'f 'g v (list 'phi v) (list 'psi v))
              (ass))))))
     (proof-leaves)))))
(qed 'antiderivative-sub)
(topic! 'antiderivative-sub 'analysis)
(alias! 'antiderivative-sub
        "Proposition 4.8 (difference)"
        "a difference of antiderivatives is an antiderivative of the difference")

;;; ... and the same statement one level up, in IS-ANTIDERIVABLE.
(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'phi (list 'FORALL 'psi (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IS-ANTIDERIVABLE phi a b)
      (list 'IMPLIES '(IS-ANTIDERIVABLE psi a b)
        (list 'IS-ANTIDERIVABLE at-sub-phi 'a 'b)))))))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi a b))
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE psi a b))
  (dk-ai-head! 'FORSOME)
  (dk-ai-head! 'FORSOME)
  ;; the two existentials bind the SAME name, so read each eigenvariable off the
  ;; formula that says WHICH function it is an antiderivative of.
  (let* ((wit (lambda (fn)
                (cadr (car (filter (lambda (z) (and (pair? z)
                                                    (eq? (car z) 'IS-ANTIDERIVATIVE)
                                                    (eq? (caddr z) fn)))
                                   (dk-asms))))))
         (fv (wit 'phi))
         (gv (wit 'psi)))
    (mac 'IS-ANTIDERIVABLE)
    (ew (list 'VNB-LAMBDA 'x 'RR (list '- (list fv 'x) (list gv 'x))))
    (fact 'antiderivative-sub fv gv 'phi 'psi 'a 'b)
    (ass))))
(qed 'antiderivable-sub)
(topic! 'antiderivable-sub 'analysis)
(alias! 'antiderivable-sub
        "a difference of antiderivable functions is antiderivable")
