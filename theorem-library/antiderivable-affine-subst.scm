;;; antiderivable-affine-subst.scm -- ANTIDERIVABILITY SURVIVES AN AFFINE CHANGE
;;; OF VARIABLE, and with it the rung-3 form of the Bernstein approximants.
;;;
;;; THE GAP THIS CLOSES.  `bernstein-uniform-approximation-ccint'
;;; (bernstein-ccint.scm) names its approximant
;;;
;;;     BERNSTEIN-POLY(f o A, n, U(x)),      U(x) = (x - a) recip(b - a),
;;;
;;; a Bernstein polynomial IN THE UNIT COORDINATE, while
;;; `bernstein-poly-antiderivable' (bernstein-antiderivable.scm) is about
;;; x |-> BERNSTEIN-POLY(g, n, x).  Those are different maps, and the rung-3
;;; assembly needs the first one.  The bridge is the substitution lemma:
;;;
;;;     phi antiderivable on [aa,bb],  A(t) = cc + lam.t,  lam /= 0
;;;        ==>  t |-> phi(A(t))  antiderivable on [p,q],
;;;
;;; with antiderivative  recip(lam) . (Phi o A).  NOTHING analytic happens here:
;;; the derivative clause is `deriv-chain' composed with `deriv-affine' and then
;;; scaled by `deriv-scalar-mult', and the continuity clause is
;;; `compose-continuous-at' composed with `affine-continuous-at' and then scaled
;;; by `scale-continuous-at'.  The only arithmetic is
;;; recip(lam).(M.lam) = M, one `rr-recip-inverse' and two `crs'.
;;;
;;; DO NOT instead redo the P(n) induction of bernstein-antiderivable.scm in the
;;; unit coordinate: its base case needs x |-> U(x)^j antiderivable, which is the
;;; binomial expansion again, and there is no C(n,k) in this tree.
;;;
;;; WHY FIVE THEOREMS AND NOT ONE.
;;;
;;;  1. `antiderivable-affine-subst' is the engine, and it is stated for lam /= 0
;;;     with the interval bookkeeping HANDED IN as two universals -- A carries
;;;     [p,q] into [aa,bb], and it carries the OPEN (p,q) into the OPEN (aa,bb).
;;;     Both are needed and they are not the same statement: Def 4.6 asks for
;;;     continuity of the antiderivative on the CLOSED interval and
;;;     differentiability on the OPEN one, so the closed containment alone leaves
;;;     the derivative clause with a point that may sit on the boundary, where
;;;     the hypothesis says nothing.  Handing them in rather than deriving them
;;;     is what keeps the lemma sign-agnostic: with lam < 0 the affine map
;;;     reverses the interval, and no single formula in aa, bb covers both signs.
;;;  2. `antiderivable-affine-subst-pos' specialises to 0 < lam and computes the
;;;     two universals from monotonicity (`rr-le-scale-nonneg',
;;;     `rr-lt-scale-pos', then one Farkas certificate each), so the image
;;;     interval is literally [A(p), A(q)].  This is the form a caller wants.
;;;  3. `antiderivable-affine-subst-pos-transfer' is (2) stated in TRANSFER form
;;;     -- the conclusion is about any psi constrained by a pointwise `==' to
;;;     t |-> phi(A(t)), not about that literal lambda.  It is not decoration:
;;;     see the trap below.
;;;  4. `bernstein-poly-unit-coordinate-antiderivable' is the rung, for an
;;;     arbitrary g : RR -> RR.
;;;  5. `bernstein-ccint-approximant-antiderivable' is (4) at g = f o A, which is
;;;     the term `bernstein-uniform-approximation-ccint' estimates against (up to
;;;     the name of one bound variable -- see the note at `afs-aff'), spelled out
;;;     so the assembly cites it with no bookkeeping of its own.
;;;
;;; THE TRAP THAT BOUGHT (3), and it is the `lam-b' obligation trap of CLAUDE.md
;;; one level in.  Instantiating (2) at phi := VNB-LAMBDA x RR. BERNSTEIN-POLY(g,n,x)
;;; makes its conclusion speak about
;;;
;;;     VNB-LAMBDA x RR. (VNB-LAMBDA x RR. BERNSTEIN-POLY(g,n,x))(cc + lam.x)
;;;
;;; -- a redex sitting UNDER a binder.  `lam-b-h' reduces every redex of the
;;; formula it is handed, so on (IN <that lambda applied to v> RR) it reduces the
;;; inner one too, and the (IN cc + lam.x RR) that reduction owes is posted in a
;;; context where `x' is FREE: an open leaf nothing can close, reported only as
;;; "have!: THUNK left the side goal open".  With phi a VARIABLE the nesting does
;;; not arise, so the transfer form -- whose hypothesis mentions phi applied, not
;;; a lambda inside a lambda -- has one redex per beta and no owed leaf.
;;;
;;; A lambda inside a lambda has a SECOND cost, and the suite is what says so:
;;; when the two binders carry the SAME name it is a shadowing binder, which
;;; `case-fold-audit' reports and nothing on screen shows.  Section 5 is the one
;;; statement here that nests one VNB-LAMBDA inside another -- the inner one is
;;; the affine map A, substituted for `g' -- and its inner binder is `x_' for
;;; exactly that reason.
;;;
;;; Needs bernstein-antiderivable (bernstein-poly-antiderivable), bernstein-ccint
;;; (ccint-parts, affine-continuous-at), chain-rule (deriv-chain),
;;; directional-derivative (deriv-affine, affine-lam-in-fun), deriv-polynomial
;;; (deriv-scalar-mult), continuity-scale (scale-continuous-at, scale-lam-in-fun),
;;; continuity-compose (compose-continuous-at), compose-apply-proof (compose-type),
;;; antiderivative (IS-ANTIDERIVATIVE / IS-ANTIDERIVABLE), series-antiderivable
;;; (antiderivable-integrand-transfer, antiderivable-fn-in-fun), ccint-basics
;;; (ccint-membership), rr-order-basics and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `afs-' prefix) --------------------

(define (afs-check name)
  (if (not (proof-done? *ps*))
      (error "antiderivable-affine-subst: proof did not close" name
             (expression->string (dk-goal)))))

;; `dk-peel-to!' gives up after 8 peels; the engine below has ten antecedents.
(define (afs-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 24) (error "afs-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

(define (afs-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; `have!' of a formula the context already carries is a self-loop, and `have!'
;; says so and stops.  Ask first.
(define (afs-need! f) (if (not (member f (dk-asms))) (have! f)))

;; `di' splits a conjunctive GOAL one level per call; split every AND leaf.
(define (afs-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;; Fourier-Motzkin over the context's ORDER facts.  Equations are deliberately
;; NOT included: `contra--usable-indices' would accept them (an `=' is
;; arithmetic in shape), and the one equation these proofs carry --
;; lam.recip(lam) = 1 -- contributes an opaque product atom that makes the whole
;; call fail with "goal not a linear-RR consequence", blaming the goal.  Nothing
;; below needs an equation as an ineq premise.
(define (afs-order-indices)
  (let loop ((l (dk-asms)) (k 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <=)))
           (loop (cdr l) (+ k 1) (cons k acc)))
          (else (loop (cdr l) (+ k 1) acc)))))
(define (afs-ineq!) (apply ineq (afs-order-indices)))

;; beta-reduce the goal to a fixed point (`lam-b' takes one redex per call)
(define (afs-beta*!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (> n 10) 'stop (begin (lam-b) (if (equal? g (dk-goal)) 'done (loop (+ n 1))))))))

;;; ---- the shapes ------------------------------------------------------

(define afs-af  '(VNB-LAMBDA x RR (+ ck (* lam x))))       ; A(t) = cc + lam.t
(define afs-psi '(VNB-LAMBDA x RR (phi (+ ck (* lam x))))) ; t |-> phi(A(t))
(define afs-rl  '(recip lam))
(define afs-Apt '(+ ck (* lam t_)))

(define (afs-at v) (list '+ 'ck (list '* 'lam v)))

;; A(t) in RR, for a real t
(define (afs-real-A! v)
  (afs-need! (list 'AND '(IN lam RR) (list 'IN v 'RR)))
  (fact 'rr-mul-in-rr 'lam v)
  (afs-need! (list 'AND '(IN ck RR) (list 'IN (list '* 'lam v) 'RR)))
  (fact 'rr-add-in-rr 'ck (list '* 'lam v)))

;; A carries [p,q] into [aa,bb] ...
(define afs-maps-in
  (forall-guarded 't_ '(IN t_ (CCINT p_ q_)) (list 'IN afs-Apt '(CCINT aa bb))))
;; ... and the OPEN (p,q) into the OPEN (aa,bb).  Def 4.6 differentiates on the
;; open interval, so the closed containment does not serve here.
(define afs-maps-int
  (forall-guarded 't_
    (conjuncts->and (list '(IN t_ RR) '(< p_ t_) '(< t_ q_)))
    (conjuncts->and (list (list '< 'aa afs-Apt) (list '< afs-Apt 'bb)))))

;;; =====================================================================
;;; 1.  THE ENGINE.  lam /= 0, the interval bookkeeping handed in.
;;;
;;; The witness is  G = t |-> recip(lam) . (F o A)(t),  written with the COMPOSE
;;; and the scaling LITERALLY as `compose-type', `scale-lam-in-fun',
;;; `scale-continuous-at' and `deriv-scalar-mult' produce them, so not one
;;; pointwise transfer is needed anywhere in this proof.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi ck lam p_ q_ aa bb)
      (list '(IN phi (FUN RR RR)) '(IN ck RR) '(IN lam RR) '(NOT (= lam 0))
            '(IN p_ RR) '(IN q_ RR) '(< p_ q_)
            '(IS-ANTIDERIVABLE phi aa bb)
            afs-maps-in afs-maps-int)
      (list 'IS-ANTIDERIVABLE afs-psi 'p_ 'q_))))
  (afs-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'rr-is-set)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi aa bb))
  (let ((afs-F (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
    (dk-split! (dk-landed-1
      (lambda () (mac-h 'IS-ANTIDERIVATIVE (list 'IS-ANTIDERIVATIVE afs-F 'phi 'aa 'bb)))))
    ;; the two universals of Def 4.6, taken on the head of their CONSEQUENT --
    ;; never by position; the context also holds the two interval universals.
    (let* ((afs-univ (lambda (head)
                       (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                     (dk-contains? z head)))
                                    (dk-asms)))))
           (afs-cf   (afs-univ 'IS-CONTINUOUS-AT))
           (afs-df   (afs-univ 'IS-DIFF-AT))
           (afs-comp (list 'COMPOSE afs-F afs-af))
           (afs-G    (list 'VNB-LAMBDA 'x 'RR (list '* afs-rl (list afs-comp 'x)))))

      (afs-need! '(AND (IN ck RR) (IN lam RR)))
      (fact 'affine-lam-in-fun 'ck 'lam)                   ; A : RR -> RR
      (afs-need! (list 'AND (list 'IN afs-af '(FUN RR RR))
                            (list 'IN afs-F '(FUN RR RR))))
      (fact 'compose-type 'RR 'RR 'RR afs-F afs-af)        ; F o A : RR -> RR
      (afs-need! '(AND (IN lam RR) (NOT (= lam 0))))
      (fact 'rr-recip-closed 'lam)
      (fact 'rr-recip-inverse 'lam)                        ; lam.recip(lam) = 1
      (fact 'scale-lam-in-fun afs-rl afs-comp)             ; G : RR -> RR

      ;; the integrand is a map RR -> RR.  `lam-t' opens TWO leaves.
      (have! (list 'IN afs-psi '(FUN RR RR))
        (lambda ()
          (for-each
           (lambda (leaf)
             (dk-focus! leaf)
             (if (eq? (car (dk-goal)) 'FORALL)
                 (let ((v (afs-di-var!)))
                   (afs-real-A! v)
                   (fact 'fun-apply-type-c 'phi 'RR 'RR (afs-at v))
                   (ass))
                 (begin (fact 'rr-is-set) (ass))))
           (dk-opened (lambda () (lam-t))))))

      (mac 'IS-ANTIDERIVABLE)
      (ew afs-G)
      (mac 'IS-ANTIDERIVATIVE)
      (afs-split-goal!)
      (for-each
       (lambda (nd)
         (dk-focus! nd)
         (let ((gl (dk-goal)))
           (cond
            ((memq (car gl) '(IN <)) (ass))
            ((eq? (car (cadr (caddr gl))) 'IN)              ; continuity clause
             (let ((v (afs-di-var!)))
               (dk-split! (dk-fact! 'ccint-parts 'p_ 'q_ v))
               ;; affine-continuous-at's antecedent is a three-way AND, which
               ;; `fact' will not split: without it the citation lands the
               ;; IMPLICATION and every citation after it lands another.
               (afs-need! (list 'AND '(IN ck RR)
                                (list 'AND '(IN lam RR) (list 'IN v 'RR))))
               (fact 'affine-continuous-at 'ck 'lam v)
               (inst+ afs-maps-in v)                       ; A(v) in [aa,bb]
               (inst+ afs-cf (afs-at v))                   ; F continuous there
               (have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS afs-F (list afs-af v))
                      (lambda () (lam-b) (ass)))
               (fact 'compose-continuous-at afs-F afs-af v)
               (fact 'scale-continuous-at afs-rl afs-comp v)
               (ass)))
            (else                                          ; derivative clause
             (di)
             (dk-split! (dk-landed-1 (lambda () (di))))
             (let* ((th (caddr (dk-goal)))
                    (av (afs-at th))
                    (mv (list 'phi av)))
               ;; `inst+' does not detach a conjunctive antecedent and the split
               ;; above took the guard apart, so the AND goes back first.
               (afs-need! (list 'AND (list 'IN th 'RR)
                                (list 'AND (list '< 'p_ th) (list '< th 'q_))))
               (afs-real-A! th)
               (dk-split! (dk-deepest (lambda () (inst+ afs-maps-int th))))
               (afs-need! (list 'AND (list 'IN av 'RR)
                                (list 'AND (list '< 'aa av) (list '< av 'bb))))
               (inst+ afs-df av)                           ; F'(A(th)) = phi(A(th))
               (have! (list 'IS-DIFF-AT afs-F (list afs-af th) mv)
                      (lambda () (lam-b) (ass)))
               (afs-need! (list 'AND '(IN ck RR)
                                (list 'AND '(IN lam RR) (list 'IN th 'RR))))
               (fact 'deriv-affine 'ck 'lam th)            ; A'(th) = lam
               (fact 'deriv-chain afs-af afs-F th 'lam mv) ; (F o A)' = phi(A).lam
               (fact 'deriv-scalar-mult afs-rl afs-comp th (list '* mv 'lam))
               (fact 'fun-apply-type-c 'phi 'RR 'RR av)
               (lam-b)                                     ; PSI(th) -> phi(A(th))
               ;; the value:  M = recip(lam).(M.lam).  The rewrite goes onto the
               ;; GOAL and in this direction because M sits inside the other
               ;; side; the reverse would rewrite that copy too.
               (let ((v1 (list '* afs-rl (list '* mv 'lam)))
                     (v2 (list '* (list '* 'lam afs-rl) mv)))
                 (have! (list '= mv v1)
                   (lambda ()
                     (have! (list '= v1 v2) (lambda () (crs)))
                     (subst (list '= v1 v2))
                     (subst (list '= (list '* 'lam afs-rl) 1))
                     (crs)))
                 (subst (list '= mv v1)))
               (ass))))))
       (proof-leaves))))))
(afs-check 'antiderivable-affine-subst)
(qed 'antiderivable-affine-subst)
(topic! 'antiderivable-affine-subst 'analysis)
(alias! 'antiderivable-affine-subst
        "antiderivability survives an affine change of variable"
        "t |-> phi(cc + lam.t) is antiderivable where phi is, with antiderivative recip(lam).(Phi o A)")

;;; =====================================================================
;;; 2.  0 < lam:  the image interval is [A(p), A(q)], computed here.
;;;
;;; Two monotonicity citations and one Farkas certificate per endpoint.  The
;;; products lam.p, lam.t, lam.q are opaque atoms to `ineq' -- it does not
;;; normalise monomials -- so each is typed real before the first call and the
;;; ORDER between them comes from `rr-le-scale-nonneg' / `rr-lt-scale-pos', not
;;; from the oracle.
;;; =====================================================================

(define afs2-aa '(+ ck (* lam p_)))
(define afs2-bb '(+ ck (* lam q_)))
(define afs2-mi (forall-guarded 't_ '(IN t_ (CCINT p_ q_))
                  (list 'IN afs-Apt (list 'CCINT afs2-aa afs2-bb))))
(define afs2-mint (forall-guarded 't_
                    (conjuncts->and (list '(IN t_ RR) '(< p_ t_) '(< t_ q_)))
                    (conjuncts->and (list (list '< afs2-aa afs-Apt)
                                          (list '< afs-Apt afs2-bb)))))

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi ck lam p_ q_)
      (list '(IN phi (FUN RR RR)) '(IN ck RR) '(IN lam RR) '(< 0 lam)
            '(IN p_ RR) '(IN q_ RR) '(< p_ q_)
            (list 'IS-ANTIDERIVABLE 'phi afs2-aa afs2-bb))
      (list 'IS-ANTIDERIVABLE afs-psi 'p_ 'q_))))
  (afs-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'rr-zero-in)
  (fact 'rr-pos-ne-zero 'lam)
  (fact 'rr-lt-implies-le 0 'lam)
  (afs-real-A! 'p_)
  (afs-real-A! 'q_)

  (have! afs2-mi
    (lambda ()
      (let ((v (afs-di-var!)))
        (dk-split! (dk-fact! 'ccint-parts 'p_ 'q_ v))
        (afs-real-A! v)
        (afs-need! (list 'AND '(<= 0 lam) (list '<= 'p_ v)))
        (fact 'rr-le-scale-nonneg 'lam 'p_ v)
        (afs-need! (list 'AND '(<= 0 lam) (list '<= v 'q_)))
        (fact 'rr-le-scale-nonneg 'lam v 'q_)
        (for-each (lambda (nd) (dk-focus! nd)
                    (if (eq? (car (dk-goal)) 'IN) (ass) (afs-ineq!)))
                  (dk-opened (lambda () (mac 'ccint-membership) (afs-split-goal!)))))))

  (have! afs2-mint
    (lambda ()
      (di)
      (let* ((lnd (dk-landed-1 (lambda () (di))))
             (v   (cadr (cadr lnd))))
        (dk-split! lnd)
        (afs-real-A! v)
        (afs-need! (list 'AND '(< 0 lam) (list '< 'p_ v)))
        (fact 'rr-lt-scale-pos 'lam 'p_ v)
        (afs-need! (list 'AND '(< 0 lam) (list '< v 'q_)))
        (fact 'rr-lt-scale-pos 'lam v 'q_)
        (for-each (lambda (nd) (dk-focus! nd) (afs-ineq!))
                  (dk-opened (lambda () (afs-split-goal!)))))))

  (fact 'antiderivable-affine-subst 'phi 'ck 'lam 'p_ 'q_ afs2-aa afs2-bb)
  (ass)))
(afs-check 'antiderivable-affine-subst-pos)
(qed 'antiderivable-affine-subst-pos)
(topic! 'antiderivable-affine-subst-pos 'analysis)
(alias! 'antiderivable-affine-subst-pos
        "an increasing affine change of variable preserves antiderivability")

;;; =====================================================================
;;; 3.  ... in TRANSFER form.  See the header: this is what lets a caller whose
;;; integrand is a functoid term, rather than the literal lambda the lemma
;;; builds, use it at all -- and it is one `antiderivable-integrand-transfer'.
;;; =====================================================================

(define afs-pw (forall-guarded 'x_ '(IN x_ RR)
                 (list '== '(psi x_) '(phi (+ ck (* lam x_))))))

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(phi psi ck lam p_ q_)
      (list '(IN phi (FUN RR RR)) '(IN psi (FUN RR RR)) '(IN ck RR) '(IN lam RR)
            '(< 0 lam) '(IN p_ RR) '(IN q_ RR) '(< p_ q_)
            (list 'IS-ANTIDERIVABLE 'phi afs2-aa afs2-bb)
            afs-pw)
      '(IS-ANTIDERIVABLE psi p_ q_))))
  (afs-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'antiderivable-affine-subst-pos 'phi 'ck 'lam 'p_ 'q_)
  (have! (forall-guarded 'x_ '(IN x_ RR) (list '== '(psi x_) (list afs-psi 'x_)))
    (lambda ()
      (let ((v (afs-di-var!)))
        (lam-b)
        (inst+ afs-pw v)
        (ass))))
  (fact 'antiderivable-integrand-transfer afs-psi 'psi 'p_ 'q_)
  (ass)))
(afs-check 'antiderivable-affine-subst-pos-transfer)
(qed 'antiderivable-affine-subst-pos-transfer)
(topic! 'antiderivable-affine-subst-pos-transfer 'analysis)
(alias! 'antiderivable-affine-subst-pos-transfer
        "the affine substitution lemma, stated for any map agreeing pointwise with the substituted integrand")

;;; =====================================================================
;;; 4.  THE RUNG.  x |-> BERNSTEIN-POLY(g, n, U(x)) is antiderivable on [a,b],
;;; where U(x) = (x - a) recip(b - a) is the unit coordinate of [a,b].
;;;
;;; U is the affine map with lam = recip(b-a) > 0 and cc = (0-a) recip(b-a), and
;;; `bernstein-poly-antiderivable' holds on EVERY nondegenerate interval, so it
;;; is cited at [U(a), U(b)] directly -- there is no need to know that those two
;;; terms are 0 and 1, and no proof here does.
;;; =====================================================================

(define afs-r   '(recip (- b a)))
(define afs-cc0 (list '* '(- 0 a) afs-r))
(define afs-phi '(VNB-LAMBDA x RR (BERNSTEIN-POLY g n_ x)))
(define afs-tgt (list 'VNB-LAMBDA 'x 'RR
                      (list 'BERNSTEIN-POLY 'g 'n_ (list '* '(- x a) afs-r))))
(define (afs-uu v) (list '+ afs-cc0 (list '* afs-r v)))     ; cc + lam.v
(define (afs-vv v) (list '* (list '- v 'a) afs-r))          ; U(v)
(define afs3-aa (list '+ afs-cc0 (list '* afs-r 'a)))
(define afs3-bb (list '+ afs-cc0 (list '* afs-r 'b)))

;; everything U(v) and cc + lam.v need, for a real v
(define (afs3-real! v)
  (fact 'rr-sub-in-rr v 'a)
  (afs-need! (list 'AND (list 'IN (list '- v 'a) 'RR) (list 'IN afs-r 'RR)))
  (fact 'rr-mul-in-rr (list '- v 'a) afs-r)
  (afs-need! (list 'AND (list 'IN afs-r 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-in-rr afs-r v)
  (afs-need! (list 'AND (list 'IN afs-cc0 'RR) (list 'IN (list '* afs-r v) 'RR)))
  (fact 'rr-add-in-rr afs-cc0 (list '* afs-r v)))

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(g n_ a b)
      (list '(IN g (FUN RR RR)) '(IN n_ NN) '(NOT (= n_ 0))
            '(AND (IN a RR) (AND (IN b RR) (< a b))))
      (list 'IS-ANTIDERIVABLE afs-tgt 'a 'b))))
  (afs-peel-to! 'IS-ANTIDERIVABLE)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (fact 'rr-zero-in)
  (fact 'rr-is-set)
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'rr-sub-in-rr 0 'a)
  (fact 'rr-lt-diff-pos 'a 'b)
  (fact 'rr-pos-ne-zero '(- b a))
  (afs-need! '(AND (IN (- b a) RR) (NOT (= (- b a) 0))))
  (fact 'rr-recip-closed '(- b a))
  (fact 'rr-recip-pos '(- b a))                        ; 0 < recip(b-a)
  (afs-need! (list 'AND '(IN (- 0 a) RR) (list 'IN afs-r 'RR)))
  (fact 'rr-mul-in-rr '(- 0 a) afs-r)                  ; cc in RR
  (afs3-real! 'a)
  (afs3-real! 'b)
  (afs-need! (list 'AND (list 'IN afs-cc0 'RR) (list 'IN (list '* afs-r 'a) 'RR)))
  (fact 'rr-add-in-rr afs-cc0 (list '* afs-r 'a))
  (afs-need! (list 'AND (list 'IN afs-cc0 'RR) (list 'IN (list '* afs-r 'b) 'RR)))
  (fact 'rr-add-in-rr afs-cc0 (list '* afs-r 'b))
  (afs-need! (list 'AND (list '< 0 afs-r) '(< a b)))
  (fact 'rr-lt-scale-pos afs-r 'a 'b)
  (have! (list '< afs3-aa afs3-bb) (lambda () (afs-ineq!)))
  (afs-need! (list 'AND (list 'IN afs3-aa 'RR)
                   (list 'AND (list 'IN afs3-bb 'RR) (list '< afs3-aa afs3-bb))))
  (fact 'bernstein-poly-antiderivable 'g 'n_ afs3-aa afs3-bb)
  (fact 'antiderivable-fn-in-fun afs-phi afs3-aa afs3-bb)

  ;; the target is a map RR -> RR: its value at v IS phi(U(v)), and phi is a
  ;; function by the citation just above.  ONE redex per `lam-b-h' here -- phi
  ;; is a lambda whose body holds no lambda -- which is the whole point of
  ;; reaching the value through phi rather than through the substituted lambda.
  (have! (list 'IN afs-tgt '(FUN RR RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (car (dk-goal)) 'FORALL)
             (let ((v (afs-di-var!)))
               (afs3-real! v)
               (fact 'fun-apply-type-c afs-phi 'RR 'RR (afs-vv v))
               (lam-b-h (list 'IN (list afs-phi (afs-vv v)) 'RR))
               (ass))
             (begin (fact 'rr-is-set) (ass))))
       (dk-opened (lambda () (lam-t))))))

  ;; the transfer hypothesis:  TGT(x) == phi(cc + lam.x), i.e. U(x) written the
  ;; two ways.  `crs' proves (v-a).r = (0-a).r + r.v; the rewrite goes onto the
  ;; LEFT side, which does not occur inside the right.
  (have! (forall-guarded 'x_ '(IN x_ RR)
           (list '== (list afs-tgt 'x_) (list afs-phi (afs-uu 'x_))))
    (lambda ()
      (let ((v (afs-di-var!)))
        (afs3-real! v)
        (afs-beta*!)
        (have! (list '= (afs-vv v) (afs-uu v)) (lambda () (crs)))
        (subst (list '= (afs-vv v) (afs-uu v)))
        (qrfl))))
  (fact 'antiderivable-affine-subst-pos-transfer afs-phi afs-tgt afs-cc0 afs-r 'a 'b)
  (ass)))
(afs-check 'bernstein-poly-unit-coordinate-antiderivable)
(qed 'bernstein-poly-unit-coordinate-antiderivable)
(topic! 'bernstein-poly-unit-coordinate-antiderivable 'analysis)
(alias! 'bernstein-poly-unit-coordinate-antiderivable
        "the Bernstein approximant in the unit coordinate of [a,b] is antiderivable on [a,b]"
        "rung 3(c) of the integration arc: the approximants of bernstein-uniform-approximation-ccint are antiderivable")


;;; =====================================================================
;;; 5.  THE APPROXIMANT OF `bernstein-uniform-approximation-ccint', VERBATIM.
;;;
;;; Section 4 is stated for an arbitrary g : RR -> RR, which is the useful
;;; generality; Theorem 5.2 on [a,b] uses it at g = f o A, A(t) = a + (b-a)t.
;;; Spelling that instance out costs three citations and saves the rung-3
;;; assembly from having to re-derive (IN COMPOSE(f,A) (FUN RR RR)) at the point
;;; of use -- the term below is character-for-character the one
;;; bernstein-uniform-approximation-ccint estimates against.
;;; =====================================================================

;; A(t) = a + (b-a)t, the map bernstein-ccint.scm calls `bc-aff'.  Its binder
;; carries the project's trailing underscore because this lambda is substituted
;; INSIDE another VNB-LAMBDA below (for `g' in section 4's statement, whose own
;; binder is `x'), and a VNB-LAMBDA x nested in a VNB-LAMBDA x is a shadowing
;; binder: `case-fold-audit' reports it, the printer round-trips it faithfully,
;; and nothing on screen shows it.  bc-aff spells the binder `x'; the two terms
;; are therefore the same up to that one bound name, which is all any citation
;; of either can see.
(define afs-aff '(VNB-LAMBDA x_ RR (+ a (* (- b a) x_))))
(define afs-fa  (list 'COMPOSE 'f afs-aff))
(define afs-fa-tgt
  (list 'VNB-LAMBDA 'x 'RR
        (list 'BERNSTEIN-POLY afs-fa 'n_ (list '* '(- x a) afs-r))))

(quietly (lambda ()
  (sp (make-wff
    (forall-guarded '(f n_ a b)
      (list '(IN f (FUN RR RR)) '(IN n_ NN) '(NOT (= n_ 0))
            '(AND (IN a RR) (AND (IN b RR) (< a b))))
      (list 'IS-ANTIDERIVABLE afs-fa-tgt 'a 'b))))
  (afs-peel-to! 'IS-ANTIDERIVABLE)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (fact 'rr-is-set)
  (fact 'rr-sub-in-rr 'b 'a)
  (afs-need! '(AND (IN a RR) (IN (- b a) RR)))
  (fact 'affine-lam-in-fun 'a '(- b a))
  (afs-need! (list 'AND (list 'IN afs-aff '(FUN RR RR)) '(IN f (FUN RR RR))))
  (fact 'compose-type 'RR 'RR 'RR 'f afs-aff)
  ;; `dk-split!' above `ai'-ed the guard, and `ai' REPLACES a conjunction with
  ;; its conjuncts -- so the AND goes back before the citation, or `fact' stops
  ;; at the antecedent it cannot detach and lands the IMPLICATION, silently.
  (afs-need! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (fact 'bernstein-poly-unit-coordinate-antiderivable afs-fa 'n_ 'a 'b)
  (ass)))
(afs-check 'bernstein-ccint-approximant-antiderivable)
(qed 'bernstein-ccint-approximant-antiderivable)
(topic! 'bernstein-ccint-approximant-antiderivable 'analysis)
(alias! 'bernstein-ccint-approximant-antiderivable
        "the approximants of Theorem 5.2 on [a,b] are antiderivable on [a,b]")
