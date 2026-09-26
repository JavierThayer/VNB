;;; theorem-library/mvt-cluster-readoffs.scm
;;;
;;; Four asserted leaves of the MVT/Rolle cluster, PROVEN.  Each is a read-off
;;; of a definition or a two-theorem composition; none needed an estimate.
;;;
;;;   diff-value-real          IS-DIFF-AT(f,a,L)  =>  L in RR
;;;                            A projection of IS-DIFF-AT (its third conjunct).
;;;                            `diff-at-value-in-rr' (directional-derivative.scm)
;;;                            is the same statement, but that file loads AFTER
;;;                            the first citer (mvt-proof.scm), so it is re-proved
;;;                            here, in place, under the name the citers use.
;;;   deriv-neg                IS-DIFF-AT(f,a,L)  =>  IS-DIFF-AT(z |-> -f(z), a, -L)
;;;                            The constant-multiple rule at c = -1
;;;                            (`deriv-scalar-mult'), carried to the literal
;;;                            negation lambda by `diff-transfer-ptwise-eq';
;;;                            typing by `neg-fun-in-fun', the pointwise `=='
;;;                            by one `lam-b' (it reduces both redexes) and one `crs', the value -L =
;;;                            (-1).L by `crs'.
;;;   max-val-strict-interior  c in [a,b], h(a) = h(b), h(a) < h(c)  =>  a < c < b
;;;   min-val-strict-interior  c in [a,b], h(a) = h(b), h(c) < h(a)  =>  a < c < b
;;;                            `ccint-membership' gives a <= c <= b; `<' unfolds
;;;                            to `<= and not =', and each `not' half is refuted
;;;                            by rewriting the offending equation into the
;;;                            strict hypothesis's own `not =' conjunct.  No
;;;                            typing of h is needed: the partial `=' in the
;;;                            hypothesis h(a) = h(b) supplies definedness.
;;;
;;; Statements reproduced VERBATIM from their support sites:
;;;   diff-value-real            theorem-library/mvt-proof.scm:66
;;;   deriv-neg                  theorem-library/differentiation.scm:249
;;;   max-val-strict-interior    theorem-library/rolle-proof.scm:113
;;;   min-val-strict-interior    theorem-library/rolle-proof.scm:119
;;;
;;; LOAD WINDOW: after theorem-library/deriv-polynomial (deriv-scalar-mult,
;;; the latest citation) and before theorem-library/interior-extremum-proof
;;; (the earliest citer of deriv-neg; rolle-proof and mvt-proof, the citers of
;;; the other three, follow it immediately).  In load.scm's 0-based order that
;;; is [350, 370]: deriv-polynomial is 349, interior-extremum-proof 370.
;;; Every other citation is far earlier: equality-basics 151, order-predicates
;;; (`<') 39, neg-continuous 264, differentiation 275, diff-transfer 276,
;;; ccint-basics 321; rr-one-in / rr-neg-closed / fun-apply-type-c are base.
;;;
;;; Helper prefix: mcr-.

;;; ---- shared helpers ----------------------------------------------------

;; `ai' every AND / FORSOME assumption to exhaustion (the IS-DIFF-AT unfold is
;; a right-nested tower with a FORSOME in the middle).
(define (mcr-split-ands!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))

;; read a conjunct of an IS-DIFF-AT hypothesis WITHOUT destroying it: `mac-h'
;; REPLACES the assumption it unfolds, so the unfold happens on a have! side
;; branch and the main branch keeps IS-DIFF-AT intact for the next citation.
(define (mcr-proj! hyp claim)
  (have! claim (lambda () (mac-h 'IS-DIFF-AT hyp) (mcr-split-ands!) (ass))))

;; di, returning the eigenvariable of the guard it landed
(define (mcr-di-var!)
  (cadr (car (dk-landed (lambda () (di))))))

(define (mcr-asm-find pred what)
  (or (any-pred pred (dk-asms)) (error "mvt-cluster-readoffs: no assumption" what)))

;;; =====================================================================
;;; (1) diff-value-real -- the third conjunct of IS-DIFF-AT.
;;; =====================================================================

(sp (make-wff
  '(FORALL f (FORALL a (FORALL L (IMPLIES (IS-DIFF-AT f a L) (IN L RR)))))))
(dk-peel-to! 'IN)
(mac-h 'IS-DIFF-AT (mcr-asm-find (dk-head? 'IS-DIFF-AT) 'IS-DIFF-AT))
(mcr-split-ands!)
(ass)
(qed 'diff-value-real)
(topic! 'diff-value-real 'analysis)

;;; =====================================================================
;;; (2) deriv-neg -- the constant-multiple rule at c = -1, transferred.
;;; =====================================================================

(sp (make-wff
  '(FORALL f (FORALL a (FORALL L
     (IMPLIES (IS-DIFF-AT f a L)
       (IS-DIFF-AT (VNB-LAMBDA z RR (- (f z))) a (- L))))))))
(dk-peel-to! 'IS-DIFF-AT)

;;; everything read off the GOAL, which names each eigenvariable in its role
(define dn-lam (cadr (dk-goal)))                    ; lambda z in RR. -f(z)
(define dn-pt  (caddr (dk-goal)))                   ; the point
(define dn-f   (car (cadr (cadddr dn-lam))))        ; f, out of (- (f z))
(define dn-dl  (cadr (cadddr (dk-goal))))           ; L, out of (- L)
(define dn-hyp (list 'IS-DIFF-AT dn-f dn-pt dn-dl))

;;; the three typings `crs' and `fun-apply-type-c' will want, read off the
;;; hypothesis on side branches (see mcr-proj!)
(mcr-proj! dn-hyp (list 'IN dn-f '(FUN RR RR)))
(mcr-proj! dn-hyp (list 'IN dn-pt 'RR))
(mcr-proj! dn-hyp (list 'IN dn-dl 'RR))

;;; c = -1 is a real
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)                             ; (IN (- 1) RR)

;;; the scalar rule: lambda x. (-1).f(x) is differentiable at pt with value (-1).L
(define dn-scal (list 'VNB-LAMBDA 'x 'RR (list '* '(- 1) (list dn-f 'x))))
(define dn-sval (list '* '(- 1) dn-dl))
(fact 'deriv-scalar-mult '(- 1) dn-f dn-pt dn-dl)

;;; transfer to the literal negation lambda: its typing ...
(have! (list 'IN dn-lam '(FUN RR RR))
  (lambda () (fact 'neg-fun-in-fun dn-f) (ass)))
;;; ... and the pointwise agreement -f(x) == (-1).f(x), stated with `==' as the
;;; transfer asks; the arithmetic is done on the `=' form and carried across by
;;; one `subst', leaving t == t for `qrfl'.
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dn-lam 'x_) (list dn-scal 'x_))))
  (lambda ()
    (let ((v (mcr-di-var!)))
      (fact 'fun-apply-type-c dn-f 'RR 'RR v)       ; (IN (f v) RR), for crs
      (lam-b)                                       ; ONE call reduces both redexes
      (let ((lhs (list '- (list dn-f v)))
            (rhs (list '* '(- 1) (list dn-f v))))
        (have! (list '= lhs rhs) (lambda () (crs)))
        (subst (list '= lhs rhs))
        (qrfl)))))
(fact 'diff-transfer-ptwise-eq dn-lam dn-scal dn-pt dn-sval)

;;; the value: -L = (-1).L
(have! (list '= (list '- dn-dl) dn-sval) (lambda () (crs)))
(subst (list '= (list '- dn-dl) dn-sval))
(ass)
(qed 'deriv-neg)
(topic! 'deriv-neg 'analysis)

;;; =====================================================================
;;; (3)/(4) the interior-position helpers of Rolle's theorem.
;;; One driver, parameterised by the strict hypothesis's orientation.
;;; =====================================================================

;;; Context after the peel: (IN c (CCINT a b)), (= (h a) (h b)), STRICT, where
;;; STRICT is (< (h a) (h c)) or (< (h c) (h a)); goal (AND (< a c) (< c b)).
;;; The goal names a, c, b; the equation names h.
(define (mcr-interior!)
  (let* ((g   (dk-goal))
         (va  (cadr (cadr g)))  (vc (caddr (cadr g)))  (vb (caddr (caddr g)))
         (eqh (mcr-asm-find (dk-head? '=) '=))              ; (= (h a) (h b))
         (ha  (cadr eqh))  (hb (caddr eqh))
         (strict (mcr-asm-find (dk-head? '<) '<)))
    ;; a <= c, c <= b out of the membership; STRICT into `<=' and `not ='
    (mac-h 'ccint-membership (list 'IN vc (list 'CCINT va vb)))
    (mcr-split-ands!)
    (mac-h '< strict)
    (mcr-split-ands!)
    (let* ((neg (mcr-asm-find (dk-head? 'NOT) 'NOT))       ; (NOT (= (h _) (h _)))
           (pos (cadr neg)))
      ;; prove the equation STRICT forbids, given the offending endpoint equation
      ;; `other' = a or b with (= vc other) (or its mirror) in context
      (define (refute! other)
        (have! pos
          (lambda ()
            (subst (list '= vc other))                    ; c -> a, or c -> b
            (let ((gg (dk-goal)))
              (cond ((any-pred (lambda (s) (alpha-equiv? s gg)) (dk-asms)) (ass))
                    ((equal? (cadr gg) (caddr gg))        ; (= (h a) (h a))
                     (fact 'eq-sym ha hb) (fact 'eq-trans ha hb ha) (ass))
                    (else (fact 'eq-sym ha hb) (ass))))))  ; (= (h b) (h a))
        (ai neg))                                         ; not-elim closes FALSITY
      (for-each
       (lambda (half)                                     ; (< a c), then (< c b)
         (dk-focus! half)
         (let ((other (if (equal? (cadr (dk-goal)) vc) vb va)))
           (mac '<)                                       ; (AND (<= _ _) (NOT (= _ _)))
           (for-each
            (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'NOT)
                  (begin (di) (refute! other))            ; assume the equation
                  (ass)))
            (dk-opened (lambda () (di))))))
       (dk-opened (lambda () (di)))))))

(sp (make-wff
  '(FORALL h (FORALL a (FORALL b (FORALL c
     (IMPLIES (IN c (CCINT a b)) (IMPLIES (= (h a) (h b)) (IMPLIES (< (h a) (h c))
       (AND (< a c) (< c b)))))))))))
(dk-peel-to! 'AND)
(mcr-interior!)
(qed 'max-val-strict-interior)
(topic! 'max-val-strict-interior 'analysis)

(sp (make-wff
  '(FORALL h (FORALL a (FORALL b (FORALL c
     (IMPLIES (IN c (CCINT a b)) (IMPLIES (= (h a) (h b)) (IMPLIES (< (h c) (h a))
       (AND (< a c) (< c b)))))))))))
(dk-peel-to! 'AND)
(mcr-interior!)
(qed 'min-val-strict-interior)
(topic! 'min-val-strict-interior 'analysis)
