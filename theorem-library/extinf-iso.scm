;;; extinf-iso.scm -- calculus.pdf 1.13 with <= REFLECTED: what neg-inf-below-reals buys, and
;;; the one comparison it does not decide.  Agent EXT-INF, 2026-10-26.
;;; DESTINATION: theorem-library/extinf-iso.scm.  Library: analysis.
;;; LOAD WINDOW: after rabasics-extline2 (ccint-rr-star-iso-bijection, ccint-rr-star-iso-strict)
;;; and after extinf-points / the new primitive neg-inf-below-reals; no citer.
;;;
;;; F = VNB-LAMBDA(x, [-1, 1], IF(x = 1, POS-INF, IF(x = -1, NEG-INF, x / (1 - |x|)))), the map of
;;; RA-BASICS (scratchpad/rabasics/rabasics-extline2.scm), copied literally.
;;;
;;;   rr-star-le-refl                       x in RR-STAR  =>  x <= x
;;;   rr-star-le-antisymm-given-ends        NOT (POS-INF <= NEG-INF)  =>  <= is antisymmetric on
;;;                                         RR-STAR
;;;   ccint-rr-star-iso-mono                u <= v in [-1, 1]  =>  F(u) <= F(v)
;;;   ccint-rr-star-iso-reflects-given-ends NOT (POS-INF <= NEG-INF)  =>
;;;                                         (F(u) <= F(v)  =>  u <= v)  on [-1, 1]
;;;
;;; WHY THE REFLECTION CARRIES AN ANTECEDENT (finding).  With pos-inf-above-reals and
;;; neg-inf-below-reals every comparison between a real and an infinity is decided, and so is
;;; every comparison of an infinity with itself.  ONE comparison is not: POS-INF <= NEG-INF.
;;; The extended-reals axioms (rr-star-membership, the two bounds, the two strictness axioms,
;;; neg-inf-not-in-rr) and the RR order axioms (all guarded on IN _ RR) hold in the model of
;;; the two-point extension in which, in addition, POS-INF <= NEG-INF; there F(1) = POS-INF <=
;;; NEG-INF = F(-1) while NOT (1 <= -1).  So "F(u) <= F(v) => u <= v" is NOT derivable, and
;;; neither are antisymmetry or transitivity of <= on RR-STAR (POS-INF <= NEG-INF <= POS-INF
;;; with POS-INF /= NEG-INF; POS-INF <= NEG-INF <= 0 with NOT (POS-INF <= 0)).  The single
;;; fact NOT (POS-INF <= NEG-INF) closes every case; it is carried here as an antecedent, and
;;; the theorems become unconditional the day it is in the library (a primitive-shelf decision
;;; for the user: `pos-inf-not-below-neg-inf', or transitivity of <= on RR-STAR, from which it
;;; follows by neg-inf-lower-bound at 0 and pos-inf-above-reals).
;;; Helper prefix: eio-.

(define eio-dom '(CCINT (- 1) 1))
(define eio-F
  (list 'VNB-LAMBDA 'x eio-dom
        (list 'IF '(= x 1) 'POS-INF
              (list 'IF '(= x (- 1)) 'NEG-INF (list '/ 'x (list '- 1 '(abs x)))))))
(define eio-ends '(NOT (<= POS-INF NEG-INF)))

(define (eio-vars landed)
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)))

(define (eio-and! . fs)
  (let ((c (let loop ((l fs)) (if (null? (cdr l)) (car l) (list 'AND (car l) (loop (cdr l)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))))

;;; use-cases that skips a branch hash-consing already grounded
(define (eio-use-cases! disjuncts . bodies)
  (let* ((result (use-cases disjuncts))
         (ob     (cases-obligation result))
         (cs     (cdr (assq 'cases result))))
    (if ob (error "eio-use-cases!: the disjunction is not in context" disjuncts))
    (if (not (= (length cs) (length bodies)))
        (error "eio-use-cases!: branch count" (length cs) (length bodies)))
    (for-each (lambda (mc body)
                (if (not (sequent-node-grounded? (cdr mc)))
                    (begin (dk-focus! (cdr mc)) (body))))
              cs bodies)))

;;; TM in RR-STAR in context: three cases, real / POS-INF / NEG-INF
(define (eio-star-cases! tm real! pinf! ninf!)
  (let ((d (list 'OR (list 'IN tm 'RR) (list 'OR (list '= tm 'POS-INF) (list '= tm 'NEG-INF)))))
    (if (not (dk-asm? d))
        (dk-have! d
          (lambda ()
            (let ((i (dk-cite! 'rr-star-membership tm)))
              (if (dk-only! i (list 'IN tm 'RR-STAR)) (prop))))))
    (eio-use-cases! (list (list 'IN tm 'RR) (list '= tm 'POS-INF) (list '= tm 'NEG-INF))
                    real! pinf! ninf!)))

;;; the comparison BAD (an atom (<= A B)) follows from a context atom by putting the case
;;; equations EQS (each (= var const)) back; NEGATION! lands (NOT BAD); then close the leaf
(define (eio-refute! bad eqs negation!)
  (dk-have! bad
    (lambda ()
      (for-each (lambda (e) (if (dk-contains? (dk-goal) (caddr e)) (subst (list '= (caddr e) (cadr e)))))
                eqs)
      (ass)))
  (negation!)
  (ai (list 'NOT bad)))

;;; ---------------------------------------------------------------------------
;;; CUT 2026-10-27 (integration): the proof of `rr-star-le-refl' (x in RR-STAR => x <= x) that stood
;;; here.  It is alpha-equal to `rr-star-leq-reflexive' (theorem-library/rr-star-order-minimal.scm,
;;; loaded earlier); its one citer below now cites that name.

;;; ---------------------------------------------------------------------------
(sp (make-wff (list 'IMPLIES eio-ends
  '(FORALL x (IMPLIES (IN x RR-STAR) (FORALL y (IMPLIES (IN y RR-STAR)
     (IMPLIES (<= x y) (IMPLIES (<= y x) (= x y))))))))))
(let* ((vs (eio-vars (dk-peel!))) (x (car vs)) (y (cadr vs))
       (ex+ (list '= x 'POS-INF)) (ex- (list '= x 'NEG-INF))
       (ey+ (list '= y 'POS-INF)) (ey- (list '= y 'NEG-INF))
       (by-ax (lambda (ax tm) (lambda () (fact ax tm))))
       (by-ends (lambda () #t)))
  (eio-star-cases! x
    (lambda ()
      (eio-star-cases! y
        (lambda ()
          (eio-and! (list 'IN x 'RR) (list 'IN y 'RR))
          (eio-and! (list '<= x y) (list '<= y x))
          (dk-cite! 'rr-leq-antisymmetric x y)
          (ass))
        (lambda () (eio-refute! (list '<= 'POS-INF x) (list ey+) (by-ax 'pos-inf-above-reals x)))
        (lambda () (eio-refute! (list '<= x 'NEG-INF) (list ey-) (by-ax 'neg-inf-below-reals x)))))
    (lambda ()
      (eio-star-cases! y
        (lambda () (eio-refute! (list '<= 'POS-INF y) (list ex+) (by-ax 'pos-inf-above-reals y)))
        (lambda () (subst ex+) (subst ey+) (rfl))
        (lambda () (eio-refute! '(<= POS-INF NEG-INF) (list ex+ ey-) by-ends))))
    (lambda ()
      (eio-star-cases! y
        (lambda () (eio-refute! (list '<= y 'NEG-INF) (list ex-) (by-ax 'neg-inf-below-reals y)))
        (lambda () (eio-refute! '(<= POS-INF NEG-INF) (list ey+ ex-) by-ends))
        (lambda () (subst ex-) (subst ey-) (rfl))))))
(qed 'rr-star-le-antisymm-given-ends)
(topic! 'rr-star-le-antisymm-given-ends 'analysis)

;;; ---------------------------------------------------------------------------
;;; F(t) in RR-STAR for t in [-1, 1] in context
(define (eio-F-typed! t)
  (let ((g (list 'IN (list eio-F t) 'RR-STAR)))
    (if (not (dk-asm? g))
        (begin
          (if (not (dk-asm? (list 'IN eio-F (list 'FUN eio-dom 'RR-STAR))))
              (begin
                (fact 'ccint-rr-star-iso-bijection)
                (dk-cite! 'bijection-in-fun eio-dom 'RR-STAR eio-F)))
          (dk-cite! 'fun-apply-type-c eio-F eio-dom 'RR-STAR t)))))

(sp (make-wff (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u eio-dom)
  (list 'FORALL 'v (list 'IMPLIES (list 'IN 'v eio-dom)
    (list 'IMPLIES '(<= u v) (list '<= (list eio-F 'u) (list eio-F 'v)))))))))
(let* ((vs (eio-vars (dk-peel!))) (u (car vs)) (v (cadr vs))
       (fu (list eio-F u)) (fv (list eio-F v)))
  (eio-F-typed! u)
  (eio-F-typed! v)
  (use-em (list '= u v)
    (lambda ()
      (subst (list '= u v))
      (dk-cite! 'rr-star-leq-reflexive fv)
      (ass))
    (lambda ()
      (let ((i (dk-cite! '< u v)))
        (dk-have! (list '< u v) (lambda () (if (dk-only! i (list '<= u v) (list 'NOT (list '= u v))) (prop)))))
      (dk-cite! 'ccint-rr-star-iso-strict u v)
      (let ((i (dk-cite! '< fu fv)))
        (if (dk-only! i (list '< fu fv)) (prop))))))
(qed 'ccint-rr-star-iso-mono)
(topic! 'ccint-rr-star-iso-mono 'analysis)

;;; ---------------------------------------------------------------------------
(sp (make-wff (list 'IMPLIES eio-ends
  (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u eio-dom)
    (list 'FORALL 'v (list 'IMPLIES (list 'IN 'v eio-dom)
      (list 'IMPLIES (list '<= (list eio-F 'u) (list eio-F 'v)) '(<= u v)))))))))
(let* ((vs (eio-vars (dk-peel!))) (u (car vs)) (v (cadr vs))
       (fu (list eio-F u)) (fv (list eio-F v)))
  (dk-project! (list 'IN u 'RR) 'ccint-membership (list 'IN u eio-dom))
  (dk-project! (list 'IN v 'RR) 'ccint-membership (list 'IN v eio-dom))
  (eio-F-typed! u)
  (eio-F-typed! v)
  (eio-and! (list 'IN u 'RR) (list 'IN v 'RR))
  (dk-cite! 'rr-leq-total u v)
  (eio-use-cases! (list (list '<= u v) (list '<= v u))
    (lambda () (ass))
    (lambda ()
      (use-em (list '= v u)
        (lambda ()
          (subst (list '= v u))
          (fact 'rr-leq-reflexive u)
          (ass))
        (lambda ()
          (let ((i (dk-cite! '< v u)))
            (dk-have! (list '< v u)
              (lambda () (if (dk-only! i (list '<= v u) (list 'NOT (list '= v u))) (prop)))))
          (dk-cite! 'ccint-rr-star-iso-strict v u)
          (let ((i (dk-cite! '< fv fu)))
            (dk-have! (list '<= fv fu) (lambda () (if (dk-only! i (list '< fv fu)) (prop))))
            (dk-have! (list 'NOT (list '= fv fu)) (lambda () (if (dk-only! i (list '< fv fu)) (prop)))))
          (dk-cite! 'rr-star-le-antisymm-given-ends fu fv)
          (dk-cite! 'equality-symmetry fu fv)
          (ai (list 'NOT (list '= fv fu))))))))
(qed 'ccint-rr-star-iso-reflects-given-ends)
(topic! 'ccint-rr-star-iso-reflects-given-ends 'analysis)
