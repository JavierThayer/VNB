;;; deriv-difference.scm -- the DIFFERENCE rule for the Caratheodory derivative
;;; IS-DIFF-AT: if f has derivative L at a and g has derivative M at a, then
;;; x |-> f(x) - g(x) has derivative L - M at a.  PROVEN, `modulo 0'.
;;;
;;;   IS-DIFF-AT(f,a,L),  IS-DIFF-AT(g,a,M)
;;;      =>  IS-DIFF-AT(lambda x in RR. f(x) - g(x),  a,  L - M)
;;;
;;; WHY IT IS WANTED.  The tree had `deriv-sum', `deriv-product',
;;; `deriv-scalar-mult' and `deriv-neg' but NO difference rule, and three files
;;; pay for that in the same way: theorem-library/antiderivative.scm (line 156,
;;; "deriv-scalar-mult at c = -1 turns g into -g; deriv-sum adds"),
;;; theorem-library/cc-coords-laws.scm (line 1226, "the tree has no difference
;;; rule for IS-DIFF-AT, so the second product enters through
;;; `deriv-scalar-mult' at -1 and then `deriv-sum'") and
;;; theorem-library/taylor-proof.scm.  Each of them rebuilds the same three-step
;;; detour -- negate, add, transfer -- and each pays the transfer's pointwise
;;; lane again.  This file does it once.
;;;
;;; THE PROOF is that detour, run on the abstract statement:
;;;
;;;   1. `deriv-neg' (theorem-library/mvt-cluster-readoffs.scm):
;;;         IS-DIFF-AT(lambda z in RR. -g(z), a, -M);
;;;   2. `deriv-sum' against f:
;;;         IS-DIFF-AT(lambda x in RR. f(x) + (lambda z. -g(z))(x), a, L + (-M));
;;;   3. `diff-transfer-ptwise-eq' onto the literal difference lambda, whose
;;;      FUN typing is `sub-lam-in-fun' (theorem-library/continuity-sub.scm) and
;;;      whose pointwise agreement is one `dk-lam-b!' -- the redexes of BOTH
;;;      sides, the outer application and the nested negation lambda, go in the
;;;      same call -- plus one `crs' on f(x) - g(x) = f(x) + (-g(x));
;;;   4. the value: L - M = L + (-M), again `crs'.
;;;
;;; `deriv-neg' IS ALREADY A THEOREM and is NOT re-proved here.  The brief for
;;; batch 14-C asked for it beside `deriv-difference'; it was proven on
;;; 2026-09-14 in theorem-library/mvt-cluster-readoffs.scm (the note at
;;; theorem-library/differentiation.scm:30 records the retirement), with exactly
;;; the statement the brief describes.  A second proof would be a
;;; `proven-duplicate-audit' entry, so this file cites it instead.
;;;
;;; THE ANTECEDENTS ARE CURRIED (CLAUDE.md, "The tactics' real behaviour":
;;; `fact' auto-detaches a curried antecedent and will NOT split a conjunctive
;;; one), unlike `deriv-sum' and `deriv-product', which are older and keep the
;;; `AND' their support statements had.  Nothing cites this theorem yet, so the
;;; shape is free to be the better one.
;;;
;;; LOAD WINDOW.  lo = the position of theorem-library/mvt-cluster-readoffs
;;; (`deriv-neg'), the LATEST citation; the others are far below it:
;;; deriv-sum-product (`deriv-sum'), diff-transfer (`diff-transfer-ptwise-eq'),
;;; continuity-sub (`sub-lam-in-fun'), differentiation (IS-DIFF-AT and the
;;; `mac-h' unfold `dk-project!' uses), fun-apply-type-proof
;;; (`fun-apply-type-c'), rr-order-basics (`rr-sub-in-rr').  hi is
;;; unconstrained: nothing cites `deriv-difference' yet.  Concretely
;;; (scratchpad/window.py, 2026-09-21): lo = 2629, the load.scm line of
;;; "theorem-library/mvt-cluster-readoffs"; hi = none.  The proposed slot is the
;;; line immediately after it, where the rest of the IS-DIFF-AT cluster sits.
;;;
;;; Helper prefix: `ddf-'.

;;; ---- file-local driver helpers ---------------------------------------

(define (ddf-head e) (and (pair? e) (car e)))

;;; The three read-offs of an IS-DIFF-AT hypothesis this proof needs, taken on a
;;; `dk-project!' LANE so that the hypothesis itself survives for the citations
;;; below (`mac-h' REPLACES what it unfolds).
(define (ddf-types! fn pt val)
  (let ((hyp (list 'IS-DIFF-AT fn pt val)))
    (dk-project! (list 'IN fn '(FUN RR RR)) 'IS-DIFF-AT hyp)
    (dk-project! (list 'IN pt 'RR) 'IS-DIFF-AT hyp)
    (dk-project! (list 'IN val 'RR) 'IS-DIFF-AT hyp)))

;;; =====================================================================
;;; deriv-difference.
;;; =====================================================================

(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
        (IMPLIES (IS-DIFF-AT f a L)
        (IMPLIES (IS-DIFF-AT g a M)
          (IS-DIFF-AT (VNB-LAMBDA x RR (- (f x) (g x))) a (- L M)))))))))))
(dk-peel-to! 'IS-DIFF-AT)

;;; everything read off the GOAL, which names each eigenvariable in its role
(define ddf-lam (cadr (dk-goal)))                  ; lambda x in RR. f(x) - g(x)
(define ddf-pt  (caddr (dk-goal)))                 ; a
(define ddf-bod (cadddr ddf-lam))                  ; (- (f x) (g x))
(define ddf-f   (car (cadr ddf-bod)))              ; f
(define ddf-g   (car (caddr ddf-bod)))             ; g
(define ddf-val (cadddr (dk-goal)))                ; (- L M)
(define ddf-l   (cadr ddf-val))                    ; L
(define ddf-m   (caddr ddf-val))                   ; M

(ddf-types! ddf-f ddf-pt ddf-l)
(ddf-types! ddf-g ddf-pt ddf-m)

;;; (1) the negation of g
(define ddf-neg (dk-fact! 'deriv-neg ddf-g ddf-pt ddf-m))
(define ddf-neglam (cadr ddf-neg))                 ; lambda z in RR. -g(z)
(define ddf-negval (cadddr ddf-neg))               ; -M

;;; (2) the sum.  `deriv-sum' keeps the conjunctive antecedent of its support
;;; statement, so the AND goes in first.
(have! (list 'AND (list 'IS-DIFF-AT ddf-f ddf-pt ddf-l) ddf-neg))
(define ddf-sum (dk-fact! 'deriv-sum ddf-f ddf-neglam ddf-pt ddf-l ddf-negval))
(define ddf-sumlam (cadr ddf-sum))                 ; lambda x. f(x) + (lambda z. -g(z))(x)
(define ddf-sumval (cadddr ddf-sum))               ; L + (-M)

;;; (3) the transfer onto the literal difference lambda
(dk-have! (list 'IN ddf-lam '(FUN RR RR))
          (lambda () (fact 'sub-lam-in-fun ddf-f ddf-g) (ass)))
(dk-have! (list 'FORALL 'ddv_ (list 'IMPLIES '(IN ddv_ RR)
            (list '== (list ddf-lam 'ddv_) (list ddf-sumlam 'ddv_))))
  (lambda ()
    (di)
    (fact 'fun-apply-type-c ddf-f 'RR 'RR 'ddv_)
    (fact 'fun-apply-type-c ddf-g 'RR 'RR 'ddv_)
    (dk-lam-b!)
    (let ((lhs (list '- (list ddf-f 'ddv_) (list ddf-g 'ddv_)))
          (rhs (list '+ (list ddf-f 'ddv_) (list '- (list ddf-g 'ddv_)))))
      (have! (list '= lhs rhs) (lambda () (crs)))
      (subst (list '= lhs rhs))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq ddf-lam ddf-sumlam ddf-pt ddf-sumval)

;;; (4) the value
(have! (list '= ddf-val ddf-sumval) (lambda () (crs)))
(subst (list '= ddf-val ddf-sumval))
(ass)
(qed 'deriv-difference)
(topic! 'deriv-difference 'analysis)
(alias! 'deriv-difference
        "the derivative of a difference is the difference of the derivatives")
