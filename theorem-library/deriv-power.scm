;;; deriv-power.scm -- the POWER RULE for the real monomial, PROVEN `modulo 0'.
;;;
;;;   n in NN  =>  IS-DIFF-AT( lambda x in RR. x^(succ n),  a,  succ(n) * a^n )
;;;
;;; WHY `succ n' AND NOT `n - 1', which is what the rule is usually written
;;; with.  d/dx x^n = n.x^(n-1) is stated over NN, where `n - 1' at n = 0 is
;;; either undefined (there is no NN predecessor of 0) or, read in RR, the
;;; number -1 -- at which `power' is governed by `power-neg', a CONDITIONAL
;;; equation needing x /= 0, so the n = 0 instance would be a claim about
;;; 0 * x^(-1) that is false at x = 0 unless one also fixes 0 * undefined.  The
;;; tree's `=' is PARTIAL and would not let that pass silently, it would simply
;;; make the base case unprovable.  Writing the exponent as `succ n' quantifies
;;; over exactly the same monomials (every exponent 1, 2, 3, ... is a `succ',
;;; and x^0 is the constant map, whose derivative is `deriv-const') while
;;; keeping every exponent in NN and every `power' in the total, unconditional
;;; part of its definition (`power-zero' / `power-succ').  At n = 0 the
;;; statement reads d/dx x^1 = 1.x^0, and the proof of the base case is exactly
;;; that reading: `deriv-identity' transferred across x^1 = x.
;;;
;;; THE INDUCTION VARIABLE IS OUTERMOST, and that is not a stylistic choice:
;;; `ni' (pi-nn-induction!) tests the goal's SHAPE literally -- (FORALL n
;;; (IMPLIES (IN n NN) body)) at the top -- so a statement quantifying the point
;;; a first would not admit induction at all, and there is no undo.
;;;
;;; THE STEP IS THE PRODUCT RULE, AND THE TRANSFER IS WHAT MAKES IT USABLE.
;;; x^(succ (succ n)) = x . x^(succ n) is `power-succ', so the step is
;;; `deriv-identity' times the induction hypothesis under `deriv-product'.  But
;;; `deriv-product' concludes about the LITERAL term it builds,
;;;
;;;    lambda x in RR. (lambda x in RR. x)(x) * (lambda x in RR. x^(succ n))(x)
;;;
;;; which is not the monomial the next rung needs; and its derivative slot is
;;; likewise a term with two unreduced redexes in it.  Both gaps are closed by
;;; `diff-transfer-ptwise-eq' (theorem-library/diff-transfer.scm) plus one
;;; `subst' of the value equation -- the same division of labour
;;; `cont-transfer-ptwise-eq' does for the continuity algebra.  WITHOUT the
;;; transfer this induction cannot be written at all: rung n+1 could not consume
;;; rung n's conclusion.
;;;
;;; THE ARITHMETIC IS DONE OVER VARIABLES, NOT OVER `power'.  `crs' does not see
;;; a symbolic `power' (dyadic-weights.scm makes the same point: it declines on
;;; `recip' and crashes on `power'), and it does not see `succ' either.  So the
;;; step's value identity
;;;
;;;    succ(succ n) . a^(succ n)  =  1 . a^(succ n) + a . (succ n . a^n)
;;;
;;; is reduced to a GENERIC RR identity in three variables -- `pw-step-identity'
;;; below, (c+1)uv = 1.uv + u.(c.v), proved by `crs' -- and then INSTANTIATED at
;;; c := succ n, u := a, v := a^n, with `nn-succ-plus-one' turning
;;; succ(succ n) into succ(n) + 1 and `power-succ' turning a^(succ n) into
;;; a.a^n.  Nothing in the identity mentions a power or a successor.
;;;
;;; WHERE THIS FILE SITS, AND WHY IT IS NOT BESIDE differentiation.scm.  It
;;; cites `power-closed-at' (x real, n in NN => x^n real), which is PROVEN in
;;; theorem-library/dyadic-weights.scm -- several hundred lines further down
;;; load.scm.  The alternative was a second copy of that induction here.  The
;;; only fact this file needs from the differentiation arc that is not already
;;; in place at dyadic-weights is `deriv-product' and the transfer, both of
;;; which load with differentiation.
;;;
;;; NOT DONE, deliberately: nothing here says what a POLYNOMIAL function is.
;;; That representation is an open design question, and the monomial is
;;; unambiguous and carries the whole inductive content.
;;;
;;; Needs differentiation (IS-DIFF-AT, deriv-identity), deriv-sum-product
;;; (deriv-product), diff-transfer (diff-transfer-ptwise-eq), dyadic-weights
;;; (power-closed-at), nn-parity-proof (nn-succ-plus-one), nn-order-basics
;;; (nn-in-rr), number-systems (power-zero, power-succ, rr-subset-cc) and
;;; driver-kit (use-induction, have!, dk-*).

;;; ---- file-local driver helpers (the `dpw-' prefix) ---------------------

(define dpw-id '(VNB-LAMBDA x RR x))
(define (dpw-lam k) (list 'VNB-LAMBDA 'x 'RR (list 'power 'x k)))

;; lam-b the goal to a fixpoint; the block lambdas nest two deep in the step,
;; and every argument reduced here is already typed in RR.
(define (dpw-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;; di, returning the eigenvariable of the guard it landed
(define (dpw-di-var!)
  (cadr (car (dk-landed* (lambda () (di))))))

;;; =====================================================================
;;; (1) the generic step identity, over VARIABLES -- see the header.
;;; =====================================================================

(sp (make-wff (forall-guarded '(c u v) '((IN c RR) (IN u RR) (IN v RR))
      '(= (* (+ c 1) (* u v)) (+ (* 1 (* u v)) (* u (* c v)))))))
(dk-peel-to! '=)
(crs)
(qed 'pw-step-identity)
(topic! 'pw-step-identity 'inequalities)
(alias! 'pw-step-identity "(c+1)uv = uv + u(cv), the power rule's step arithmetic")

;;; =====================================================================
;;; (2) the monomial is a function.  `lam-t' opens TWO leaves -- the pointwise
;;; typing of the body and the SETHOOD of the domain -- and a driver expecting
;;; one leaves the other open until `qed'.
;;; =====================================================================

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (IN (VNB-LAMBDA x RR (power x n)) (FUN RR RR))))))
(di)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (begin (fact 'power-closed-at 'n (dpw-di-var!)) (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'pow-lam-in-fun)
(topic! 'pow-lam-in-fun 'analysis)
(alias! 'pow-lam-in-fun "the real monomial x |-> x^n is a function RR -> RR")

;;; =====================================================================
;;; (3) the POWER RULE.
;;; =====================================================================

(sp (make-wff
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL a (IMPLIES (IN a RR)
       (IS-DIFF-AT (VNB-LAMBDA x RR (power x (succ n))) a
                   (* (succ n) (power a n)))))))))
(define dpw-br (use-induction))

;;; ---- base: n = 0.  x^(succ 0) = x, and succ(0).a^0 = 1, so the base case
;;; IS `deriv-identity', carried across by the transfer.
(dk-focus! (cdr (assq 'base dpw-br)))
(di)
(fact 'rr-subset-cc 'a)
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(fact 'power-zero 'a)                                  ; a^0 = 1
(have! '(= (* (succ 0) (power a 0)) 1)
  (lambda () (subst '(= (power a 0) 1)) (arith)))
(subst '(= (* (succ 0) (power a 0)) 1))                ; goal value is now 1
(fact 'deriv-identity 'a)
(fact 'pow-lam-in-fun '(succ 0))
;;; the pointwise hypothesis is stated with `==', which is what the transfer
;;; asks for; the arithmetic is done on the `=' form and carried across by one
;;; `subst', leaving z == z for `qrfl'.
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list (dpw-lam '(succ 0)) 'x_) (list dpw-id 'x_))))
  (lambda ()
    (let ((z (dpw-di-var!)))
      (dpw-beta!)                                      ; goal: z^(succ 0) == z
      (fact 'rr-subset-cc z)
      (have! (list 'AND (list 'IN z 'CC) '(IN 0 NN)))
      (have! (list '= (list 'power z '(succ 0)) z)
        (lambda ()
          (fact 'power-succ z 0)
          (subst (list '= (list 'power z '(succ 0)) (list '* z (list 'power z 0))))
          (fact 'power-zero z)
          (subst (list '= (list 'power z 0) 1))        ; goal: z * 1 = z
          (crs)))
      (subst (list '= (list 'power z '(succ 0)) z))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq (dpw-lam '(succ 0)) dpw-id 'a 1)
(ass)

;;; ---- step: x^(succ (succ n)) = x . x^(succ n), so identity times the IH.
(dk-focus! (cdr (assq 'step dpw-br)))
(define dpw-n  (cdr (assq 'var dpw-br)))
(define dpw-ih (cdr (assq 'ih  dpw-br)))
(di)
(define dpw-pt (caddr (dk-goal)))                      ; the point a
(define dpw-pn  (dpw-lam (list 'succ dpw-n)))          ; lambda x. x^(succ n)
(define dpw-psn (dpw-lam (list 'succ (list 'succ dpw-n))))
(define dpw-mv  (list '* (list 'succ dpw-n) (list 'power dpw-pt dpw-n)))
(define dpw-prodlam
  (list 'VNB-LAMBDA 'x 'RR (list '* (list dpw-id 'x) (list dpw-pn 'x))))

(fact 'rr-subset-cc dpw-pt)
(fact 'nn-succ-closed dpw-n)
(fact 'nn-succ-closed (list 'succ dpw-n))
(fact 'nn-in-rr (list 'succ dpw-n))
(fact 'power-closed-at dpw-n dpw-pt)
(fact 'deriv-identity dpw-pt)                          ; IS-DIFF-AT(id, a, 1)
(inst+ dpw-ih dpw-pt)                                  ; IS-DIFF-AT(x^(succ n), a, MV)
(have! (list 'AND (list 'IS-DIFF-AT dpw-id dpw-pt 1)
                  (list 'IS-DIFF-AT dpw-pn dpw-pt dpw-mv)))
(define dpw-prodf (dk-fact! 'deriv-product dpw-id dpw-pn dpw-pt 1 dpw-mv))
(define dpw-value (cadddr dpw-prodf))                  ; 1.PN(a) + id(a).MV, unreduced

;;; the value: succ(succ n).a^(succ n) = the product rule's derivative slot.
(have! (list '= (list '* (list 'succ (list 'succ dpw-n))
                         (list 'power dpw-pt (list 'succ dpw-n)))
                dpw-value)
  (lambda ()
    (dpw-beta!)
    (fact 'nn-succ-plus-one (list 'succ dpw-n))        ; succ(succ n) = succ(n)+1
    (subst (list '= (list 'succ (list 'succ dpw-n)) (list '+ (list 'succ dpw-n) 1)))
    (have! (list 'AND (list 'IN dpw-pt 'CC) (list 'IN dpw-n 'NN)))
    (fact 'power-succ dpw-pt dpw-n)                    ; a^(succ n) = a.a^n
    (subst (list '= (list 'power dpw-pt (list 'succ dpw-n))
                    (list '* dpw-pt (list 'power dpw-pt dpw-n))))
    (fact 'pw-step-identity (list 'succ dpw-n) dpw-pt (list 'power dpw-pt dpw-n))
    (ass)))
(subst (list '= (list '* (list 'succ (list 'succ dpw-n))
                         (list 'power dpw-pt (list 'succ dpw-n)))
                dpw-value))

;;; the function: the monomial agrees pointwise with the product rule's lambda.
(fact 'pow-lam-in-fun (list 'succ (list 'succ dpw-n)))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
          (list '== (list dpw-psn 'x_) (list dpw-prodlam 'x_))))
  (lambda ()
    (let ((z (dpw-di-var!)))
      (dpw-beta!)                                 ; z^(succ(succ n)) == z.z^(succ n)
      (fact 'rr-subset-cc z)
      (have! (list 'AND (list 'IN z 'CC) (list 'IN (list 'succ dpw-n) 'NN)))
      (fact 'power-succ z (list 'succ dpw-n))     ; the `=' form, then carry across
      (subst (list '= (list 'power z (list 'succ (list 'succ dpw-n)))
                      (list '* z (list 'power z (list 'succ dpw-n)))))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq dpw-psn dpw-prodlam dpw-pt dpw-value)
(ass)
(qed 'deriv-power)
(topic! 'deriv-power 'analysis)
(alias! 'deriv-power "the power rule: the derivative of x^(n+1) is (n+1)x^n")
