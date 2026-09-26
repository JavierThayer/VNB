;;; zen-step.scm -- ZEN's three recursion equations, collapsed into ONE.
;;;
;;; Rung 1 of Zermelo L1 (the CARD-free "every set bijects with an ordinal
;;; segment"), and the rung the rest of that construction was waiting on.
;;;
;;; ZEN is installed by def-by-ord-recursion in THREE differently shaped
;;; equations (zero / successor / limit), so every downstream step would have to
;;; case-split on which one applies.  zen-step is the single equation that holds
;;; at EVERY ordinal:
;;;
;;;   forall alpha in ORD, X.
;;;     ZEN(X,alpha) = CHOICE { y in X : forall c ORD-LT alpha. ZEN(X,c) /= y }
;;;
;;; Alpha is quantified OUTERMOST so that (tfi3) applies to the goal as stated:
;;; `di' peels the whole leading FORALL prefix in one step, so a statement
;;; reading (FORALL X (FORALL alpha ...)) could not be brought to the shape the
;;; rule wants.  The induction hypothesis is never used -- tfi3 is doing duty
;;; here as ordinal CASE ANALYSIS (every ordinal is 0, a successor, or a limit),
;;; which is the only reason the three equations cover the class.
;;;
;;; Two facts land here, both `modulo 0':
;;;
;;;   ord-lt-succ-iff-le   al, cc in ORD |-  cc < succ al  <->  cc <= al
;;;   zen-step             the uniform equation above
;;;
;;; The bridge is what the successor case needs, since ZEN-succ writes its bound
;;; `<= alpha' while the uniform form writes `< succ alpha'.
;;;
;;; HALF OF IT ALREADY EXISTED, in disjunctive form: `ord-lt-succ-cases'
;;; (zorn-route-two.scm) is `b < succ a  =>  b < a OR b = a', which with
;;; ord-lt-iff is this file's left-to-right direction.  It is NOT cited here for
;;; a mundane reason -- zorn-route-two loads after this file (load.scm:688 to
;;; :683) -- and proving the IFF outright from the order axioms keeps the file
;;; self-contained and costs about fifteen lines.  If the two ever want to be
;;; one lemma, the ordinal facts belong together beside the ord-* axioms, above
;;; both consumers; that is the move, not a cross-citation between two proofs
;;; sixty files apart.
;;;
;;; The base case is the awkward one, exactly as predicted: ZEN-zero says
;;; `ZEN(X,0) = CHOICE X' while the uniform form says CHOICE of a separation
;;; whose condition is vacuous, so it needs (a) nothing is ORD-LT 0 -- from
;;; ord-zero-least and antisymmetry -- and (b) class-extensionality to identify
;;; that vacuous separation with X.  Writing the zero case in SEP shape to dodge
;;; this would make the base equation refer to ZEN below 0 and turn
;;; def-by-ord-recursion into def-constant with arbitrary equations; do not.
;;;
;;; Needs: ordinals.scm (def-by-ord-recursion, the ord-* axioms, tfi3),
;;; interactive + qed/proof-debt, driver-kit (have!, use-cases, dk-*).

;;; ---- driver helpers (zs- prefix) ------------------------------------
(define (zs-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (zs-peel!)
  (let lp () (let* ((g (zs-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (zs-pick! ls pred what)
  (dk-focus! (or (any-pred (lambda (s) (pred (dk-goal-of s))) ls)
                 (error "zen-step: no leaf" what))))
(define (zs-goal-is g) (lambda (h) (equal? h g)))

;;; =====================================================================
;;; the bridge:  c ORD-LT succ(al)  <->  c ORD-LE al
;;; =====================================================================
(define ZS-SA '(succ_ORD al))

(sp (make-wff '(FORALL al (IMPLIES (IN al ORD)
                 (FORALL cz (IMPLIES (IN cz ORD)
                   (IFF (ORD-LT cz (succ_ORD al)) (ORD-LE cz al))))))))
(zs-peel!)
(define zs-two (dk-opened (lambda () (di))))

;;; (=>)  cc < succ al  |-  cc <= al
(zs-pick! zs-two (zs-goal-is '(ORD-LE cz al)) "bridge =>")
(fact 'ord-lt-iff 'cz ZS-SA)
(ai (list 'IFF (list 'ORD-LT 'cz ZS-SA)
          (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA)))))
(detach! (list 'IMPLIES (list 'ORD-LT 'cz ZS-SA)
               (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA)))))
(dk-split! (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA))))
(have! '(AND (IN al ORD) (IN cz ORD)))
(fact 'ord-le-total 'al 'cz)
(use-cases '(OR (ORD-LE al cz) (ORD-LE cz al))
  (lambda ()
    (pbc)                                             ; assume NOT (cc <= al)
    (have! '(NOT (= al cz))                           ; else reflexivity gives it
      (lambda ()
        (di)
        (have! '(ORD-LE cz al)
          (lambda () (fact 'ord-le-refl 'cz) (subst '(= al cz)) (ass)))
        (ai '(NOT (ORD-LE cz al)))))
    (have! '(AND (ORD-LE al cz) (NOT (= al cz))))
    (fact 'ord-lt-iff 'al 'cz)
    (ai '(IFF (ORD-LT al cz) (AND (ORD-LE al cz) (NOT (= al cz)))))
    (detach! '(IMPLIES (AND (ORD-LE al cz) (NOT (= al cz))) (ORD-LT al cz)))
    (have! '(AND (IN al ORD) (AND (IN cz ORD) (ORD-LT al cz))))
    (fact 'ord-succ-immediate 'al 'cz)                ; succ al <= cc
    (have! (list 'AND (list 'ORD-LE ZS-SA 'cz) (list 'ORD-LE 'cz ZS-SA)))
    (fact 'ord-le-antisymm ZS-SA 'cz)                 ; succ al = cc
    (have! (list '= 'cz ZS-SA) (lambda () (fact 'eq-sym ZS-SA 'cz) (ass)))
    (ai (list 'NOT (list '= 'cz ZS-SA))))
  (lambda () (ass)))

;;; (<=)  cc <= al  |-  cc < succ al
(zs-pick! zs-two (zs-goal-is (list 'ORD-LT 'cz ZS-SA)) "bridge <=")
(fact 'ord-succ-above 'al)
(fact 'ord-lt-iff 'al ZS-SA)
(ai (list 'IFF (list 'ORD-LT 'al ZS-SA)
          (list 'AND (list 'ORD-LE 'al ZS-SA) (list 'NOT (list '= 'al ZS-SA)))))
(detach! (list 'IMPLIES (list 'ORD-LT 'al ZS-SA)
               (list 'AND (list 'ORD-LE 'al ZS-SA) (list 'NOT (list '= 'al ZS-SA)))))
(dk-split! (list 'AND (list 'ORD-LE 'al ZS-SA) (list 'NOT (list '= 'al ZS-SA))))
(have! (list 'AND '(ORD-LE cz al) (list 'ORD-LE 'al ZS-SA)))
(fact 'ord-le-trans 'cz 'al ZS-SA)
(have! (list 'NOT (list '= 'cz ZS-SA))
  (lambda ()
    (di)
    (have! (list 'ORD-LE ZS-SA 'al)
      (lambda () (fact 'eq-sym 'cz ZS-SA) (subst (list '= ZS-SA 'cz)) (ass)))
    (have! (list 'AND (list 'ORD-LE ZS-SA 'al) (list 'ORD-LE 'al ZS-SA)))
    (fact 'ord-le-antisymm ZS-SA 'al)
    (have! (list '= 'al ZS-SA) (lambda () (fact 'eq-sym ZS-SA 'al) (ass)))
    (ai (list 'NOT (list '= 'al ZS-SA)))))
(have! (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA))))
(fact 'ord-lt-iff 'cz ZS-SA)
(ai (list 'IFF (list 'ORD-LT 'cz ZS-SA)
          (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA)))))
(detach! (list 'IMPLIES (list 'AND (list 'ORD-LE 'cz ZS-SA) (list 'NOT (list '= 'cz ZS-SA)))
               (list 'ORD-LT 'cz ZS-SA)))
(ass)

(qed 'ord-lt-succ-iff-le)
(topic! 'ord-lt-succ-iff-le 'inequalities)

;;; =====================================================================
;;; ZEN, and the uniform step law
;;; =====================================================================
(register-constant! 'ZEN 'defined-fn)
(def-by-ord-recursion 'ZEN '(X)
  '(CHOICE X)
  '(alpha val)
  '(CHOICE (SEP y_ X (FORALL c_ (IMPLIES (ORD-LE c_ alpha) (NOT (= (ZEN X c_) y_))))))
  '(lam)
  '(CHOICE (SEP y_ X (FORALL c_ (IMPLIES (ORD-LT c_ lam) (NOT (= (ZEN X c_) y_)))))))

;; the avoid-set at BOUND, over carrier XV; BOUND is a formula in c_
(define (zs-sep xv bound)
  (list 'SEP 'y_ xv (list 'FORALL 'c_ (list 'IMPLIES bound
                                            (list 'NOT (list '= (list 'ZEN xv 'c_) 'y_))))))
(define (zs-lt a) (list 'ORD-LT 'c_ a))
(define (zs-le a) (list 'ORD-LE 'c_ a))

;; the body of that SEP, at element YV -- what sep-me lands and sep-mi owes
(define (zs-body xv yv bound)
  (list 'FORALL 'c_ (list 'IMPLIES bound (list 'NOT (list '= (list 'ZEN xv 'c_) yv)))))

;; c_v < 0 is impossible: 0 is least, and antisymmetry then says c_v IS 0.
(define (zs-nothing-below-zero! cv)
  (fact 'ord-lt-iff cv 0)
  (ai (list 'IFF (list 'ORD-LT cv 0)
            (list 'AND (list 'ORD-LE cv 0) (list 'NOT (list '= cv 0)))))
  (detach! (list 'IMPLIES (list 'ORD-LT cv 0)
                 (list 'AND (list 'ORD-LE cv 0) (list 'NOT (list '= cv 0)))))
  (dk-split! (list 'AND (list 'ORD-LE cv 0) (list 'NOT (list '= cv 0))))
  (fact 'ord-le-closure cv 0)
  (dk-split! (list 'AND (list 'IN cv 'ORD) '(IN 0 ORD)))
  (fact 'ord-zero-least cv)
  (have! (list 'AND (list 'ORD-LE cv 0) (list 'ORD-LE 0 cv)))
  (fact 'ord-le-antisymm cv 0)
  (ai (list 'NOT (list '= cv 0))))

;; Two classes with the same members are equal.  The antecedent is taken FROM
;; THE PROVER -- `fact' instantiates class-extensionality's (FORALL x (IFF (IN x
;; A) (IN x B))) at A := a separation over the carrier, and the carrier here IS
;; the eigenvariable `x', so capture-avoidance renames that binder to something
;; we cannot predict.  Writing the antecedent by hand instead produced a
;; DIFFERENT formula (binder `x' capturing the carrier `x'), which auto-detach
;; then failed to match -- and, worse, whose side goal closed.
(define (zs-find-asm pred what)
  (or (any-pred pred (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
      (error "zen-step: no assumption" what)))

(define (zs-class-ext! a b prove-iff)
  (fact 'class-extensionality a b)
  (let* ((target (list '= a b))
         (impl (zs-find-asm (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                             (equal? (caddr f) target)))
                            "class-extensionality at these two classes")))
    (have! (cadr impl) prove-iff)
    (detach! impl)))

;; A separation's membership goal (IN yv (SEP ...)), given (IN yv XV) in context
;; and a PROVE-BODY thunk for the body obligation.
(define (zs-sep-intro! xv yv bound prove-body)
  (let ((subs (dk-opened (lambda () (sep-mi)))))
    (zs-pick! subs (zs-goal-is (list 'IN yv xv)) "sep-mi carrier")
    (ass)
    (zs-pick! subs (zs-goal-is (zs-body xv yv bound)) "sep-mi body")
    (prove-body)))

(sp (make-wff (list 'FORALL 'alpha (list 'IMPLIES '(IN alpha ORD)
      (list 'FORALL 'X
        (list '= '(ZEN X alpha) (list 'CHOICE (zs-sep 'X (zs-lt 'alpha)))))))))

(define zs-cases (dk-opened (lambda () (tfi3))))
(define (zs-case-base? g)  (and (pair? g) (eq? (car g) 'FORALL)
                                (pair? (caddr g)) (eq? (car (caddr g)) '=)))
(define (zs-case-succ? g)  (and (pair? g) (eq? (car g) 'FORALL)
                                (pair? (caddr g)) (eq? (car (caddr g)) 'IMPLIES)
                                (eq? (car (cadr (caddr g))) 'AND)
                                (eq? (car (cadr (cadr (caddr g)))) 'IN)))
(define (zs-case-limit? g) (and (pair? g) (eq? (car g) 'FORALL)
                                (pair? (caddr g)) (eq? (car (caddr g)) 'IMPLIES)
                                (eq? (car (cadr (caddr g))) 'AND)
                                (eq? (car (cadr (cadr (caddr g)))) 'LIMIT-ORD)))

;;; ---- BASE:  ZEN(X,0) = CHOICE { y in X : nothing below 0 } = CHOICE X ----
(zs-pick! zs-cases zs-case-base? "base")
(di)                                                  ; peel X
(define zs-X0 (cadr (cadr (zs-goal))))                ; goal (= (ZEN X 0) (CHOICE ...))
(define ZS-S0 (zs-sep zs-X0 (zs-lt 0)))

(zs-class-ext! ZS-S0 zs-X0
  (lambda ()
    (di)                                              ; peel the extensionality binder
    (let* ((yv   (cadr (cadr (zs-goal))))             ; goal (IFF (IN v SEP) (IN v X))
           (both (dk-opened (lambda () (di)))))
      ;; member of the separation => member of X
      (zs-pick! both (zs-goal-is (list 'IN yv zs-X0)) "base ext =>")
      (sep-me (list 'IN yv ZS-S0))
      (ass)
      ;; member of X => member of the separation (the condition is vacuous)
      (zs-pick! both (zs-goal-is (list 'IN yv ZS-S0)) "base ext <=")
      (zs-sep-intro! zs-X0 yv (zs-lt 0)
        (lambda ()
          (zs-peel!)                                  ; peel c_ and its guard
          (let ((cv (caddr (cadr (cadr (zs-goal))))))  ; goal (NOT (= (ZEN X cv) yv))
            (di)                                      ; NOT-intro: assume the equation
            (zs-nothing-below-zero! cv)))))))

(fact 'ZEN-zero zs-X0)                                ; (= (ZEN X 0) (CHOICE X))
(subst (list '= (list 'ZEN zs-X0 0) (list 'CHOICE zs-X0)))
(subst (list '= ZS-S0 zs-X0))
(rfl)

;;; ---- SUCCESSOR:  the two bounds `<= al' and `< succ al' cut out the same set
(zs-pick! zs-cases zs-case-succ? "succ")
(di)                                                  ; peel the induction variable
(dk-split! (dk-landed-1 (lambda () (di))))            ; assume (AND (IN al ORD) IH), split it
(di)                                                  ; peel X
(define zs-Xs (cadr (cadr (zs-goal))))                ; goal (= (ZEN X (succ al)) (CHOICE ...))
(define zs-al (cadr (caddr (cadr (zs-goal)))))
(define ZS-SAL (list 'succ_ORD zs-al))
(define ZS-SLE (zs-sep zs-Xs (zs-le zs-al)))          ; what ZEN-succ produces
(define ZS-SLS (zs-sep zs-Xs (zs-lt ZS-SAL)))         ; what the uniform law wants

;; cv is an ordinal -- read off whichever comparison the branch has
(define (zs-ord-from-le! cv)
  (fact 'ord-le-closure cv zs-al)
  (dk-split! (list 'AND (list 'IN cv 'ORD) (list 'IN zs-al 'ORD))))
(define (zs-ord-from-lt! cv)
  (fact 'ord-lt-iff cv ZS-SAL)
  (ai (list 'IFF (list 'ORD-LT cv ZS-SAL)
            (list 'AND (list 'ORD-LE cv ZS-SAL) (list 'NOT (list '= cv ZS-SAL)))))
  (detach! (list 'IMPLIES (list 'ORD-LT cv ZS-SAL)
                 (list 'AND (list 'ORD-LE cv ZS-SAL) (list 'NOT (list '= cv ZS-SAL)))))
  (dk-split! (list 'AND (list 'ORD-LE cv ZS-SAL) (list 'NOT (list '= cv ZS-SAL))))
  (fact 'ord-le-closure cv ZS-SAL)
  (dk-split! (list 'AND (list 'IN cv 'ORD) (list 'IN ZS-SAL 'ORD))))
;; land the bridge at cv, in the direction asked for
(define (zs-bridge! cv want)
  (fact 'ord-lt-succ-iff-le zs-al cv)
  (ai (list 'IFF (list 'ORD-LT cv ZS-SAL) (list 'ORD-LE cv zs-al)))
  (detach! want))

(fact 'ZEN-succ zs-Xs zs-al)
(subst (list '= (list 'ZEN zs-Xs ZS-SAL) (list 'CHOICE ZS-SLE)))

(zs-class-ext! ZS-SLS ZS-SLE
  (lambda ()
    (di)
    (let* ((yv   (cadr (cadr (zs-goal))))
           (both (dk-opened (lambda () (di)))))
      ;; avoiding everything below succ al  =>  avoiding everything up to al
      (zs-pick! both (zs-goal-is (list 'IN yv ZS-SLE)) "succ ext =>")
      (let ((body-lt (dk-landed-find (lambda () (sep-me (list 'IN yv ZS-SLS)))
                                     (dk-head? 'FORALL))))
        (zs-sep-intro! zs-Xs yv (zs-le zs-al)
          (lambda ()
            (zs-peel!)
            (let ((cv (caddr (cadr (cadr (zs-goal))))))
              (zs-ord-from-le! cv)
              (zs-bridge! cv (list 'IMPLIES (list 'ORD-LE cv zs-al) (list 'ORD-LT cv ZS-SAL)))
              (inst+ body-lt cv)
              (ass)))))
      ;; ... and conversely
      (zs-pick! both (zs-goal-is (list 'IN yv ZS-SLS)) "succ ext <=")
      (let ((body-le (dk-landed-find (lambda () (sep-me (list 'IN yv ZS-SLE)))
                                     (dk-head? 'FORALL))))
        (zs-sep-intro! zs-Xs yv (zs-lt ZS-SAL)
          (lambda ()
            (zs-peel!)
            (let ((cv (caddr (cadr (cadr (zs-goal))))))
              (zs-ord-from-lt! cv)
              (zs-bridge! cv (list 'IMPLIES (list 'ORD-LT cv ZS-SAL) (list 'ORD-LE cv zs-al)))
              (inst+ body-le cv)
              (ass))))))))

(subst (list '= ZS-SLS ZS-SLE))
(rfl)

;;; ---- LIMIT:  the installed equation IS the uniform one -------------
(zs-pick! zs-cases zs-case-limit? "limit")
(di)
(dk-split! (dk-landed-1 (lambda () (di))))            ; (AND (LIMIT-ORD lam) IH)
(di)
(define zs-Xl (cadr (cadr (zs-goal))))
(define zs-lm (caddr (cadr (zs-goal))))
(fact 'ZEN-limit zs-Xl zs-lm)
(ass)

(if (proof-done? *ps*)
    (begin (qed 'zen-step)
           (topic! 'zen-step 'constructions))
    (begin
      (display "\n*** zen-step did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (sequent-node-assertion l)))
                  (newline))
                (proof-leaves))
      (error "zen-step: unfinished")))

;;; =====================================================================
;;; zen-hits:  where there is anything left to choose, ZEN chooses it.
;;;
;;;   alpha in ORD,  the avoid-set at alpha inhabited
;;;     |-  ZEN(X,alpha) IS a member of that avoid-set
;;;
;;; choice-axiom says CHOICE(A) is in A for inhabited A; zen-step says
;;; ZEN(S,alpha) IS that CHOICE.
;;;
;;; THE SET IS BOUND AS `S', NOT `X', AND THAT IS LOAD-BEARING.  choice-axiom's
;;; antecedent is (FORSOME x (IN x A)); instantiating A at a separation over the
;;; eigenvariable `x' -- which is what a binder named X produces, case-folded --
;;; puts a free `x' under that binder, so capture-avoidance renames it and the
;;; hand-written premise no longer matches.  `fact' then lands the implication
;;; undetached and the proof stalls one step later, at an `ass' whose goal reads
;;; exactly like the assumption it cannot find.  Binding the set as `S' removes
;;; the collision.  (Same trap as class-extensionality above; twice in one file.)
;;; =====================================================================
(define (ze-avoid xv a) (zs-sep xv (zs-lt a)))

(sp (make-wff (list 'FORALL 'alpha (list 'IMPLIES '(IN alpha ORD)
      (list 'FORALL 'S
        (list 'IMPLIES (list 'FORSOME 'x (list 'IN 'x (ze-avoid 'S 'alpha)))
              (list 'IN (list 'ZEN 'S 'alpha) (ze-avoid 'S 'alpha))))))))
(zs-peel!)
(define ze-h-X (cadr (cadr (zs-goal))))               ; goal (IN (ZEN X alpha) AVOID)
(define ze-h-al (caddr (cadr (zs-goal))))
(fact 'choice-axiom (ze-avoid ze-h-X ze-h-al))
(fact 'zen-step ze-h-al ze-h-X)
(subst (list '= (list 'ZEN ze-h-X ze-h-al) (list 'CHOICE (ze-avoid ze-h-X ze-h-al))))
(ass)
(qed 'zen-hits)
(topic! 'zen-hits 'constructions)

;;; =====================================================================
;;; zen-exhausts:  the enumeration RUNS OUT.
;;;
;;;   X in SET  |-  forsome alpha in ORD, nothing in X avoids every earlier stage
;;;
;;; The mathematical core of Zermelo, and the same endgame as zorn-route-two:
;;; if every stage had something left to choose, ZEN would be an injection of
;;; the whole of ORD into the set X, and ord-no-injection-into-set turns that
;;; into FALSITY by replacement and Burali-Forti.
;;;
;;; The injectivity argument is where zen-hits earns its keep: at the LATER of
;;; two stages the chosen element avoids every earlier one, so two stages cannot
;;; agree.  Totality of ORD-LE gives the two cases, and the second needs both
;;; the disequality and the equation reversed -- `subst' rewrites every
;;; occurrence, so each reversal is its own cut (the lesson zorn-route-two's
;;; z2-neq-sym! records).
;;; =====================================================================
;; Peel a guarded ordinal universal and return the EIGENVARIABLE -- taken from
;; the guard the peel just landed, never dug out of the goal.  The goal shapes
;; here differ ((FORSOME x ...) in one place, (IN (PHI av) S) in another) and
;; index-walking one of them is how this file first died, with a Scheme
;; type error rather than a proof failure.
(define (ze-peeled-ordinal!)
  (cadr (dk-landed-find (lambda () (zs-peel!))
                        (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                         (eq? (caddr f) 'ORD))))))

(define (ze-goal-exists xv)
  (list 'FORSOME 'alpha
        (list 'AND '(IN alpha ORD)
              (list 'NOT (list 'FORSOME 'x (list 'IN 'x (ze-avoid xv 'alpha)))))))

(sp (make-wff (list 'FORALL 'S (list 'IMPLIES '(IN S SET) (ze-goal-exists 'S)))))
(zs-peel!)
(define ze-X (cadr (zs-find-asm (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (eq? (caddr f) 'SET)))
                               "the set being enumerated")))
(define ZE-EX (ze-goal-exists ze-X))
(define ZE-PHI-X (list 'VNB-LAMBDA 'a_ 'ORD (list 'ZEN ze-X 'a_)))
(define ZE-ALL (list 'FORALL 'alpha (list 'IMPLIES '(IN alpha ORD)
                     (list 'FORSOME 'x (list 'IN 'x (ze-avoid ze-X 'alpha))))))

(pbc)                                                 ; assume the enumeration never runs out

;; ... which says, stage by stage, that there is always something left
(have! ZE-ALL
  (lambda ()
    (let ((av (ze-peeled-ordinal!)))
      (pbc)
      (have! ZE-EX (lambda () (ew av) (from-context!)))
      (ai (list 'NOT ZE-EX)))))

;; the enumeration is a class function ORD -> X
(have! (list 'FORALL 'alpha (list 'IMPLIES '(IN alpha ORD)
             (list 'IN (list ZE-PHI-X 'alpha) ze-X)))
  (lambda ()
    (let ((av (ze-peeled-ordinal!)))
      (lam-b)
      (inst+ ZE-ALL av)
      (fact 'zen-hits av ze-X)
      (sep-me (list 'IN (list 'ZEN ze-X av) (ze-avoid ze-X av)))
      (ass))))

;; ... and it is injective, because the later stage avoids the earlier one
(define (ze-clash! lo hi flip?)
  (if flip?
      (have! (list 'NOT (list '= lo hi))
        (lambda () (di) (fact 'eq-sym lo hi) (ai (list 'NOT (list '= hi lo))))))
  (have! (list 'AND (list 'ORD-LE lo hi) (list 'NOT (list '= lo hi))))
  (fact 'ord-lt-iff lo hi)
  (ai (list 'IFF (list 'ORD-LT lo hi)
            (list 'AND (list 'ORD-LE lo hi) (list 'NOT (list '= lo hi)))))
  (detach! (list 'IMPLIES (list 'AND (list 'ORD-LE lo hi) (list 'NOT (list '= lo hi)))
                 (list 'ORD-LT lo hi)))
  (inst+ ZE-ALL hi)
  (fact 'zen-hits hi ze-X)
  (let ((body (dk-landed-find (lambda () (sep-me (list 'IN (list 'ZEN ze-X hi)
                                                       (ze-avoid ze-X hi))))
                              (dk-head? 'FORALL))))
    (inst+ body lo))                                  ; ZEN(X,lo) /= ZEN(X,hi)
  (if flip? (fact 'eq-sym (list 'ZEN ze-X hi) (list 'ZEN ze-X lo)))
  (ai (list 'NOT (list '= (list 'ZEN ze-X lo) (list 'ZEN ze-X hi)))))

(have! (list 'FORALL 'a1_ (list 'IMPLIES '(IN a1_ ORD)
             (list 'FORALL 'a2_ (list 'IMPLIES '(IN a2_ ORD)
                   (list 'IMPLIES (list '= (list ZE-PHI-X 'a1_) (list ZE-PHI-X 'a2_))
                         '(= a1_ a2_))))))
  (lambda ()
    (zs-peel!)                                        ; a1_, a2_, and the equation
    (let* ((g  (zs-goal))                             ; goal (= a1_ a2_)
           (u  (cadr g))
           (v  (caddr g)))
      (lam-b-h (list '= (list ZE-PHI-X u) (list ZE-PHI-X v)))
      (pbc)
      (have! (list 'AND (list 'IN u 'ORD) (list 'IN v 'ORD)))
      (fact 'ord-le-total u v)
      (use-cases (list 'OR (list 'ORD-LE u v) (list 'ORD-LE v u))
        (lambda () (ze-clash! u v #f))
        (lambda () (ze-clash! v u #t))))))

(fact 'ord-no-injection-into-set ze-X ZE-PHI-X)
(ass)

(if (proof-done? *ps*)
    (begin (qed 'zen-exhausts)
           (topic! 'zen-exhausts 'constructions))
    (begin
      (display "\n*** zen-exhausts did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (sequent-node-assertion l)))
                  (newline))
                (proof-leaves))
      (error "zen-exhausts: unfinished")))
