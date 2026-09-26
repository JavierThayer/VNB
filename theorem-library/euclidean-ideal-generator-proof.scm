;;; euclidean-ideal-generator-proof.scm -- every ideal of a Euclidean ring has a
;;; generator: some b in I with I subset (b).
;;;
;;;   euclidean-ideal-has-generator :
;;;     IS-EUCLIDEAN-RING(s) and IS-IDEAL(s,I)
;;;       =>  FORSOME b. b in I and (FORALL a in I. a in PRINCIPAL-IDEAL(s,b))
;;;
;;; This is THE mathematical core of "every Euclidean ring is a PID" -- the
;;; other two lemmas of that theorem (principal-ideal-in-ideal, ideal-elt-in-
;;; carrier) are absorption and subset-def, and the theorem itself is set
;;; extensionality glue.  It was ASSERTED in structure-library/ideal.scm with a
;;; 'proof warrant whose text was a proof sketch; the sketch is now the driver.
;;;
;;; The whole argument is one `minimize!' call plus Euclidean division:
;;;
;;;   b := argmin { deg(x) : x in I, x /= 0 }              [minimize!]
;;;   a in I  =>  a = q.b + r, with r = 0 or deg(r) < deg(b)  [div-remainder]
;;;   r = a - q.b lies in I                                [ideal closure]
;;;   r /= 0 would give deg(b) <= deg(r) by minimality, contradicting
;;;     deg(r) < deg(b)                                    [nn-succ-le-antisym]
;;;   so r = 0, and a = q.b is in (b).
;;;
;;; NO CHOICE.  minimize!'s witness comes from separation-elimination on the
;;; degree set, not from the epsilon operator.  See minimize.scm.
;;;
;;; The degenerate case I = {0} is separate: b := 0, every a in I is 0, and
;;; 0 = 0.0 is in (0).
;;;
;;; TWO TRAPS, both paid for once already.
;;;   * `mac-h' REPLACES the assumption it unfolds.  Unfolding (IS-IDEAL s I) to
;;;     get at its closure conjuncts therefore DESTROYS the hypothesis that
;;;     ideal-elt-in-carrier needs.  So we do not cite that support at all: the
;;;     SUBSET conjunct plus subset-def gives x in I => x in CARR(s) directly,
;;;     and the bill is one support shorter for it.
;;;   * `minimize!' lands GUARD[v:=w] as ONE conjunction, not as its conjuncts.
;;;     Split it with `ai' before trying to detach anything against it.
;;;
;;; Needs: minimize.scm + theorem-library/nn-least-element (minimize!),
;;; ideal.scm (IS-IDEAL, PRINCIPAL-IDEAL), euclidean-ring (GAUGE,
;;; gauge-is-degree, HAS-DIV-REMAINDER), mat-equiv.scm (nn-succ-le-antisym),
;;; order-lemmas (fun-apply-type-c, eq-sym), ring.scm.

;;; ---- driver helpers (eig- prefix; a bare capital would case-fold onto a tactic)
(define (eig-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (eig-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (eig-foc! n) (dk-focus! n))
(define (eig-last) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (eig-leaves)
  (filter (lambda (n) (and (not (sequent-node-grounded? n))
                           (null? (sequent-node-in-arrows n))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
;; Both focus helpers ERROR on a miss.  One that returns #f and leaves focus put
;; hides every later mistake (CLAUDE.md, "Writing proof drivers").
(define (eig-foc-goal! g)
  (let loop ((ls (eig-leaves)))
    (cond ((null? ls) (error "eig-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (eig-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
;; Sibling or-elim branches share a goal; only the context tells them apart.
(define (eig-foc-ctx! f)
  (let loop ((ls (eig-leaves)))
    (cond ((null? ls) (error "eig-foc-ctx!: no open leaf whose context has" f))
          ((member f (map wff-formula (sequent-node-assumptions (car ls))))
           (eig-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (eig-find pred)
  (let lp ((as (eig-asms)))
    (cond ((null? as) (error "eig-find: no such assumption"))
          ((pred (car as)) (car as))
          (else (lp (cdr as))))))
(define (eig-di*)
  (let lp () (let* ((g (eig-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
;; excluded middle, as in clear-pivot-cross-proof.scm
(define (eig-em p)
  (cut (list 'OR p (list 'NOT p)))
  (let ((use-or (eig-last)))
    (pbc) (cut (list 'NOT p))
    (let ((use-notp (eig-last)))
      (di) (cut (list 'OR p (list 'NOT p)))
      (let ((u2 (eig-last))) (oi-l) (ass) (eig-foc! u2))
      (ai (list 'NOT (list 'OR p (list 'NOT p)))) (eig-foc! use-notp))
    (cut (list 'OR p (list 'NOT p)))
    (let ((u3 (eig-last))) (oi-r) (ass) (eig-foc! u3))
    (ai (list 'NOT (list 'OR p (list 'NOT p)))) (eig-foc! use-or)))
;; Split on p.  Focus lands on the p branch; the returned node is the (NOT p) one.
(define (eig-cases p) (eig-em p) (ai (list 'OR p (list 'NOT p))) (eig-last))
;; ai f, returning the assumptions it added
(define (eig-ai-new f)
  (let ((before (eig-asms)))
    (ai f)
    (filter (lambda (g) (not (member g before))) (eig-asms))))

;;; ---- shorthand for the ring operations of s
(define (eig-add x y) (list (list 'ADD 's) x y))
(define (eig-mul x y) (list (list 'MUL 's) x y))
(define (eig-neg x)   (list (list 'NEG 's) x))
(define (eig-deg x)   (list (list 'GAUGE 's) x))
(define eig-zero '(ZERO s))
(define (eig-nonzero x) (list 'NOT (list '= x eig-zero)))

;;; ===================================================================
(sp (make-wff
  '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (FORALL I (IMPLIES (IS-IDEAL s I)
       (FORSOME b (AND (IN b I)
         (FORALL a (IMPLIES (IN a I)
           (IN a (PRINCIPAL-IDEAL s b))))))))))))
(eig-di*)

;;; ---- ring coercions, and the Euclidean gauge with its division law
(fact 'euclidean-ring-is-integral-domain 's)
(fact 'integral-domain-is-commutative-ring 's)
(fact 'commutative-ring-is-ring 's)
(fact 'gauge-is-degree 's)
(ai '(AND (IN (GAUGE s) (FUN (CARR s) NN)) (HAS-DIV-REMAINDER s (GAUGE s))))
(mac-h 'HAS-DIV-REMAINDER '(HAS-DIV-REMAINDER s (GAUGE s)))
;; the only FORALL in context so far -- IS-IDEAL is still folded
(define eig-divrem (eig-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)))))

;;; ---- unfold IS-IDEAL into its usable conjuncts
(define eig-absorb
  '(FORALL r (IMPLIES (IN r (CARR s)) (FORALL a (IMPLIES (IN a I) (IN ((MUL s) r a) I))))))
(define eig-negcl '(FORALL a (IMPLIES (IN a I) (IN ((NEG s) a) I))))
(define eig-addcl
  '(FORALL a (IMPLIES (IN a I) (FORALL b (IMPLIES (IN b I) (IN ((ADD s) a b) I))))))
(define eig-k5 (list 'AND eig-negcl eig-absorb))
(define eig-k4 (list 'AND eig-addcl eig-k5))
(define eig-k3 (list 'AND '(IN (ZERO s) I) eig-k4))
(define eig-k2 (list 'AND '(SUBSET I (CARR s)) eig-k3))
(define eig-k1 (list 'AND '(IS-COMMUTATIVE-RING s) eig-k2))
(mac-h 'IS-IDEAL '(IS-IDEAL s I))
(ai eig-k1) (ai eig-k2) (ai eig-k3) (ai eig-k4) (ai eig-k5)

;;; x in I => x in CARR(s), straight off the SUBSET conjunct.  (ideal-elt-in-
;;; carrier would do it, but its hypothesis is the IS-IDEAL we just unfolded.)
(mac-h 'subset-def '(SUBSET I (CARR s)))
(define eig-sub '(FORALL x (IMPLIES (IN x I) (IN x (CARR s)))))
(define (eig-in-carr! t)
  (inst eig-sub t)
  (detach! (subst-free 'x t (caddr eig-sub))))

;;; ===================================================================
;;; Does I contain a nonzero element?
;;; ===================================================================
(define eig-guard (list 'AND '(IN x I) (eig-nonzero 'x)))
(define eig-nz (list 'FORSOME 'x eig-guard))
(define eig-zero-ideal (eig-cases eig-nz))   ; focus: the "yes" branch

;;; ===================================================================
;;; I has a nonzero element: take b of least degree among them.
;;; ===================================================================
(define eig-r (minimize! '(x) eig-guard (eig-deg 'x)))
;; minimize! leaves focus on the caller's goal.  Capture the NODE: both branches
;; of the I-has-a-nonzero-element split carry the same goal formula, so a
;; goal-shaped refocus later would land in the wrong one.
(define eig-main (proof-state-focus *ps*))
(define eig-b (car (car eig-r)))
(define eig-type (or (cadr eig-r) (error "euclidean-ideal-generator: TYPE not opened")))
;; NONEMPTY is eig-nz itself, already in context, so minimize! returns #f for it.

;;; ---- obligation: the degree of a nonzero ideal element is a natural number.
(eig-foc! eig-type)
(di) (di)
(let ((xx (cadr (cadr (eig-goal)))))     ; goal (IN ((GAUGE s) xx) NN)
  (ai (list 'AND (list 'IN xx 'I) (eig-nonzero xx)))
  (eig-in-carr! xx)
  (fact 'fun-apply-type-c '(GAUGE s) '(CARR s) 'NN xx)
  (ass))

;;; ---- back on the main branch.  minimize! lands the guard as ONE conjunction.
(eig-foc! eig-main)
(ai (list 'AND (list 'IN eig-b 'I) (eig-nonzero eig-b)))
(define eig-minim
  (eig-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                             (pair? (caddr z)) (eq? (car (caddr z)) 'IMPLIES)
                             (pair? (caddr (caddr z)))
                             (eq? (car (caddr (caddr z))) '<=)))))

(ew eig-b)
(di)
(eig-foc-goal! (list 'IN eig-b 'I)) (ass)
(eig-foc-goal! (list 'FORALL 'a (list 'IMPLIES '(IN a I)
                                      (list 'IN 'a (list 'PRINCIPAL-IDEAL 's eig-b)))))
(di)                                     ; peels a, absorbs (IN a I)
(define eig-a (cadr (eig-goal)))         ; goal (IN a (PRINCIPAL-IDEAL s b))
(define eig-concl (eig-goal))

(eig-in-carr! eig-a)
(eig-in-carr! eig-b)

;;; ---- Euclidean division of a by b:  a = q.b + r
(inst eig-divrem eig-a)
(define eig-d1 (subst-free (cadr eig-divrem) eig-a (caddr eig-divrem)))
(detach! eig-d1)
(define eig-d2 (caddr eig-d1))
(inst eig-d2 eig-b)
(define eig-d3 (subst-free (cadr eig-d2) eig-b (caddr eig-d2)))
(detach! eig-d3)
(define eig-d4 (caddr eig-d3))           ; (IMPLIES (NOT (= b 0)) (FORSOME q ...))
(detach! eig-d4)
(define eig-d5 (caddr eig-d4))

(define eig-qbody (car (eig-ai-new eig-d5)))            ; (AND (IN q (CARR s)) (FORSOME r ...))
(define eig-q (cadr (cadr eig-qbody)))
(ai eig-qbody)
(define eig-rbody (car (eig-ai-new (caddr eig-qbody)))) ; (AND (IN r (CARR s)) (AND EQ DISJ))
(define eig-rr (cadr (cadr eig-rbody)))
(ai eig-rbody)
(ai (caddr eig-rbody))
(define eig-eq   (cadr (caddr eig-rbody)))   ; (= a ((ADD s) ((MUL s) q b) r))
(define eig-disj (caddr (caddr eig-rbody)))  ; (OR (= r 0) (<= (succ (deg r)) (deg b)))

;;; ---- r = a - q.b lies in I
(define eig-qb  (eig-mul eig-q eig-b))
(define eig-sum (eig-add eig-a (eig-neg eig-qb)))
(fact 'ring-carrier-closed-mul 's eig-q eig-b)

(inst eig-absorb eig-q)                                  ; absorption at r := q
(define eig-ab0 (subst-free 'r eig-q (caddr eig-absorb)))
(detach! eig-ab0)
(define eig-ab1 (caddr eig-ab0))
(inst eig-ab1 eig-b)
(detach! (subst-free 'a eig-b (caddr eig-ab1)))          ; (IN q.b I)

(inst eig-negcl eig-qb)
(detach! (subst-free 'a eig-qb (caddr eig-negcl)))       ; (IN -(q.b) I)

(inst eig-addcl eig-a)
(define eig-ad0 (subst-free 'a eig-a (caddr eig-addcl)))
(detach! eig-ad0)
(define eig-ad1 (caddr eig-ad0))
(inst eig-ad1 (eig-neg eig-qb))
(detach! (subst-free 'b (eig-neg eig-qb) (caddr eig-ad1)))  ; (IN a + -(q.b) I)

(cut (list 'IN eig-rr 'I))
  (cut (list '= eig-sum eig-rr))
    (subst eig-eq)                       ; a -> q.b + r throughout the goal
    (crs)                                ; (q.b + r) + -(q.b) = r
  (eig-foc-goal! (list 'IN eig-rr 'I))
  (fact 'eq-sym eig-sum eig-rr)
  (subst (list '= eig-rr eig-sum))
  (ass)
(eig-foc-goal! eig-concl)

;;; ---- r = 0, or a contradiction with minimality
(define eig-r-nonzero (eig-cases (list '= eig-rr eig-zero)))   ; focus: r = 0

;;; r = 0:  a = q.b + 0 = q.b, so a is in (b).
(mac 'principal-ideal-membership)
(di)
(eig-foc-goal! (list 'IN eig-a '(CARR s))) (ass)
(eig-foc-goal! (list 'FORSOME 'r (list 'AND '(IN r (CARR s))
                                       (list '= eig-a (eig-mul 'r eig-b)))))
(ew eig-q) (di)
(eig-foc-goal! (list 'IN eig-q '(CARR s))) (ass)
(eig-foc-goal! (list '= eig-a (eig-mul eig-q eig-b)))
(subst eig-eq)
(subst (list '= eig-rr eig-zero))
(fact 'ring-add-right-id 's eig-qb)
(subst (list '= (eig-add eig-qb eig-zero) eig-qb))
(rfl)

;;; r /= 0: minimality of deg(b) contradicts deg(r) < deg(b).
(eig-foc! eig-r-nonzero)
(ai eig-disj)                            ; or-elim
;; the (= r 0) branch is refuted by this branch's own (NOT (= r 0))
(eig-foc-ctx! (list '= eig-rr eig-zero))
(ai (list 'NOT (list '= eig-rr eig-zero)))
;; the succ(deg r) <= deg b branch contradicts minimality
(eig-foc-ctx! (caddr eig-disj))
(fact 'fun-apply-type-c '(GAUGE s) '(CARR s) 'NN eig-rr)
(fact 'fun-apply-type-c '(GAUGE s) '(CARR s) 'NN eig-b)
(cut (list 'AND (list 'IN eig-rr 'I) (eig-nonzero eig-rr)))
  (di)
  (eig-foc-goal! (list 'IN eig-rr 'I)) (ass)
  (eig-foc-goal! (eig-nonzero eig-rr)) (ass)
(eig-foc-goal! eig-concl)
(inst eig-minim eig-rr)
(detach! (subst-free (cadr eig-minim) eig-rr (caddr eig-minim)))
(fact 'nn-succ-le-antisym (eig-deg eig-rr) (eig-deg eig-b))
(ai (list 'NOT (list '<= (eig-deg eig-b) (eig-deg eig-rr))))   ; not-elim closes any goal

;;; ===================================================================
;;; I = {0}: take b = 0.
;;; ===================================================================
(eig-foc! eig-zero-ideal)
(fact 'ring-zero-in 's)
(ew eig-zero)
(di)
(eig-foc-goal! (list 'IN eig-zero 'I)) (ass)
(eig-foc-goal! (list 'FORALL 'a (list 'IMPLIES '(IN a I)
                                      (list 'IN 'a (list 'PRINCIPAL-IDEAL 's eig-zero)))))
(di)
(define eig-a0 (cadr (eig-goal)))
(define eig-concl0 (eig-goal))
;; a must be 0 -- otherwise it witnesses the existential this branch denies
(cut (list '= eig-a0 eig-zero))
  (pbc)
  (cut eig-nz)
    (ew eig-a0) (di)
    (eig-foc-goal! (list 'IN eig-a0 'I)) (ass)
    (eig-foc-goal! (eig-nonzero eig-a0)) (ass)
  (eig-foc-goal! 'FALSITY)
  (ai (list 'NOT eig-nz))
(eig-foc-goal! eig-concl0)
(eig-in-carr! eig-a0)
(mac 'principal-ideal-membership)
(di)
(eig-foc-goal! (list 'IN eig-a0 '(CARR s))) (ass)
(eig-foc-goal! (list 'FORSOME 'r (list 'AND '(IN r (CARR s))
                                       (list '= eig-a0 (eig-mul 'r eig-zero)))))
(ew eig-zero) (di)
(eig-foc-goal! (list 'IN eig-zero '(CARR s))) (ass)
(eig-foc-goal! (list '= eig-a0 (eig-mul eig-zero eig-zero)))
(subst (list '= eig-a0 eig-zero))
(fact 'ring-mul-zero-left 's eig-zero)
(subst (list '= (eig-mul eig-zero eig-zero) eig-zero))
(rfl)

(qed 'euclidean-ideal-has-generator)
(topic! 'euclidean-ideal-has-generator 'algebra)
