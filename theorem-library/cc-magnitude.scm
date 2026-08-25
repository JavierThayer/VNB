;;; cc-magnitude.scm -- the complex modulus, PROVEN from its definition.
;;;
;;; WHAT CHANGED.  Until 2026-08-17 `magnitude' was characterised in
;;; number-systems.scm by five NORM-shaped axioms -- closed, nonneg, zero-iff,
;;; neg, multiplicative -- plus the triangle inequality and rr-magnitude-is-abs.
;;; That is the `abs' defect one system up: the axioms say magnitude is *a* norm
;;; and never say WHICH, nothing tied |z| to z's coordinates, and no proof could
;;; compute a modulus.  With real-part / imag-part now DEFINED, the standard
;;; definition is available (structure-library/complex.scm):
;;;
;;;     magnitude(z)  ==  SQRT( re(z)*re(z) + im(z)*im(z) )
;;;
;;; and all seven axioms become theorems.  They are deleted at their old home.
;;;
;;; WHAT IT COSTS.  SQRT is not defined in this tree; it is characterised by the
;;; `well-known' supports sqrt-nonneg / sqrt-sq / sqrt-of-sq / sqrt-mono /
;;; sqrt-mul (structure-library/real-powers.scm).  So these seven facts move
;;; from `primitive' -- contributing {} to every bill -- to theorems billing
;;; those supports at trust `well-known'.  That is a DISCLOSURE, not a
;;; regression: the assumption was always in the tree, in a symbol whose
;;; existence nobody has derived from order completeness, and it now shows on
;;; the bill of every fact that leans on it.  No other bill moves: nothing else
;;; in the library cites a magnitude axiom by name.
;;;
;;; THE MECHANISM.  One driver, `cm-mag!', does the work everywhere: given z's
;;; coordinates it lands the radicand, its nonnegativity, the SQRT typing and
;;; the modulus equation.  Every proof then reduces to real algebra:
;;;
;;;   closed / nonneg   sqrt-nonneg at re^2 + im^2 >= 0.
;;;   zero-iff          sqrt-sq turns |z| = 0 into re^2 + im^2 = 0; two
;;;                     nonnegative squares summing to 0 are each 0 (LINEAR),
;;;                     and rr-no-zero-divisors takes each root.
;;;   neg               (-x)^2 + (-y)^2 = x^2 + y^2 is a `crs' identity, and
;;;                     SQRT is a function.
;;;   mul               the Brahmagupta-Fibonacci identity
;;;                     (xu-yv)^2 + (xv+yu)^2 = (x^2+y^2)(u^2+v^2), also `crs',
;;;                     then sqrt-mul.
;;;   is-abs            a real is a + 0i, so |a| = SQRT(a*a) = abs(a) by
;;;                     sqrt-of-sq -- which is where the two moduli meet.
;;;   triangle          Cauchy-Schwarz in two dimensions, which is ALSO a `crs'
;;;                     identity: (x^2+y^2)(u^2+v^2) - (xu+yv)^2 = (xv-yu)^2.
;;;                     With `rr-le-of-sq-le' below that gives xu+yv <= |z||w|,
;;;                     hence |z+w|^2 <= (|z|+|w|)^2, and sqrt-mono finishes.
;;;
;;; NOTHING here reasons about square roots directly: every step is a ring
;;; identity, a linear consequence, or one of the five sqrt supports.
;;;
;;; TWO TRAPS, both paid for in runs:
;;;   * `ineq' certifies an atom only from an (IN t RR) in context, and an `='
;;;     is arithmetic in SHAPE -- so the equation `z = x + y i' that every proof
;;;     here carries is ACCEPTED by the oracle and then fails its own atom test
;;;     (z is complex), killing the whole call.  `cm-idx' filters premises by
;;;     the oracle's own test first.  contra.scm has the same helper for the
;;;     same reason; it loads long after this file, so this is a copy.
;;;   * `prop' has an atom cap of 12 and these contexts carry 46, so the
;;;     (OR (= t 0) (= t 0)) that rr-no-zero-divisors returns at a SQUARE is
;;;     eliminated by hand (`cm-from-same-or!').


(define (cm-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (cm-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; The atoms `ineq' would abstract a term to, mirroring vnb->linear.
(define (cm-atoms t acc)
  (cond ((number? t) acc)
        ((not (pair? t)) (if (member t acc) acc (cons t acc)))
        ((memq (car t) '(+ - binplus binneg))
         (let lp ((as (cdr t)) (acc acc))
           (if (null? as) acc (lp (cdr as) (cm-atoms (car as) acc)))))
        ((memq (car t) '(* bintimes))
         (let ((nonnum (filter (lambda (a) (not (number? a))) (cdr t))))
           (cond ((null? nonnum) acc)
                 ((null? (cdr nonnum)) (cm-atoms (car nonnum) acc))
                 (else (if (member t acc) acc (cons t acc))))))
        (else (if (member t acc) acc (cons t acc)))))

;;; The premises `ineq' can actually use: order-shaped AND with every atom
;;; certified in RR.  An `=' is arithmetic in SHAPE, so a context equation
;;; between COMPLEX terms (z = x + y i, which every proof here carries) is
;;; accepted by the oracle and then fails its own atom test, killing the whole
;;; call -- so filter first, by exactly the oracle's test.  contra.scm has the
;;; same helper for the same reason; it loads long after this file, so this is
;;; a copy rather than a call.
(define (cm-idx)
  (let* ((sqn  (proof-state-focus *ps*))
         (asms (sequent-node-assumptions sqn)))
    (let loop ((as asms) (k 1) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((f (wff-formula (car as))))
            (loop (cdr as) (+ k 1)
                  (if (and (pair? f) (= (length f) 3)
                           (memq (car f) '(< <= =))
                           (let allok ((vs (cm-atoms (caddr f) (cm-atoms (cadr f) '()))))
                             (or (null? vs)
                                 (and (ineq-atom-rr-ok? (car vs) asms '())
                                      (allok (cdr vs))))))
                      (cons k acc)
                      acc)))))))

(define (cm-ineq!) (apply ineq (cm-idx)))

;;; rr-no-zero-divisors at a SQUARE lands (OR (= t 0) (= t 0)) -- the same
;;; disjunct twice.  `prop' would close it, but only on a small context: its
;;; atom cap is 12 and these proofs carry 46, so eliminate the OR by hand.
(define (cm-from-same-or! eq)
  (for-each (lambda (k) (dk-focus! k) (ass))
            (dk-opened (lambda () (ai (list 'OR eq eq))))))

(define (cm-fvs) (apply append (map free-vars (dk-asms))))

(define (cm-obtain-here!)
  (let ((ex  (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (dk-asms)))
        (fv0 (cm-fvs)))
    (if (not ex) (error "cm-obtain-here!: no existential in context"))
    (ai ex)
    (cm-split!)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (cm-fvs))))
      (if (null? fresh) (error "cm-obtain-here!: no eigenvariable appeared"))
      (car fresh))))

;;; coordinates of ZZ (requires (IN ZZ CC)): eigenvariables cx, cy with
;;; (= ZZ (+ cx (* cy +i))), (= (real-part ZZ) cx), (= (imag-part ZZ) cy).
(define (cm-coords! zz)
  (fact 'cc-generated-by-rr zz)
  (let* ((cx (cm-obtain-here!))
         (cy (cm-obtain-here!)))
    (fact 'cc-re-im-of zz cx cy)
    (cm-split!)
    (list cx cy)))

;;; given (= (real-part ZZ) cx), (= (imag-part ZZ) cy) in context and cx, cy in
;;; RR: land the modulus equation and the closure/nonnegativity facts.
;;; Returns the radicand.
(define (cm-mag! zz cx cy)
  (let* ((sx (list '* cx cx))
         (sy (list '* cy cy))
         (p  (list '+ sx sy))
         (rt (list 'SQRT p))
         (mg (list 'magnitude zz))
         (reeq (list '= (list 'real-part zz) cx))
         (imeq (list '= (list 'imag-part zz) cy)))
    ;; the projections themselves, typed -- `ineq' certifies an atom only from an
    ;; (IN t RR) in context, and these two are atoms of every equation below.
    (fact 'real-part-in-rr zz)
    (fact 'imag-part-in-rr zz)
    (have! (list 'AND (list 'IN cx 'RR) (list 'IN cx 'RR)))
    (fact 'rr-mul-closed cx cx)
    (have! (list 'AND (list 'IN cy 'RR) (list 'IN cy 'RR)))
    (fact 'rr-mul-closed cy cy)
    (fact 'rr-sq-nonneg cx)
    (fact 'rr-sq-nonneg cy)
    (have! (list 'AND (list 'IN sx 'RR) (list 'IN sy 'RR)))
    (fact 'rr-add-closed sx sy)
    (have! (list '<= 0 p) (lambda () (cm-ineq!)))
    (have! (list 'AND (list 'IN p 'RR) (list '<= 0 p)))
    (fact 'sqrt-nonneg p)
    (ai (list 'AND (list 'IN rt 'RR) (list '<= 0 rt)))
    (have! (list '= mg rt)
           (lambda () (mac 'magnitude-def) (subst reeq) (subst imeq) (rfl)))
    p))

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (IN (magnitude z) RR)))))
(cm-peel!)
(let ((w (cm-coords! 'z)))
  (cm-mag! 'z (car w) (cadr w))
  (subst (list '= '(magnitude z) (list 'SQRT (list '+ (list '* (car w) (car w))
                                                      (list '* (cadr w) (cadr w))))))
  (ass))
(qed 'cc-magnitude-closed)
(topic! 'cc-magnitude-closed 'algebra)

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (<= 0 (magnitude z))))))
(cm-peel!)
(let ((w (cm-coords! 'z)))
  (cm-mag! 'z (car w) (cadr w))
  (subst (list '= '(magnitude z) (list 'SQRT (list '+ (list '* (car w) (car w))
                                                      (list '* (cadr w) (cadr w))))))
  (ass))
(qed 'cc-magnitude-nonneg)
(topic! 'cc-magnitude-nonneg 'inequalities)

(sp (make-wff '(= (SQRT 0) 0)))
(have! '(IN 0 RR))
(have! '(<= 0 0) (lambda () (arith)))
(have! '(AND (IN 0 RR) (<= 0 0)))
(fact 'sqrt-nonneg 0)
(cm-split!)
(fact 'sqrt-sq 0)
(have! '(AND (IN (SQRT 0) RR) (IN (SQRT 0) RR)))
(fact 'rr-no-zero-divisors '(SQRT 0) '(SQRT 0))
(cm-from-same-or! '(= (SQRT 0) 0))
(qed 'sqrt-zero)
(topic! 'sqrt-zero 'inequalities)

(sp (make-wff (forall-guarded '(t_ s_) (list '(IN t_ RR) '(IN s_ RR))
      '(IMPLIES (<= 0 s_) (IMPLIES (<= (* t_ t_) (* s_ s_)) (<= t_ s_))))))
(cm-peel!)
(fact 'rr-le-abs 't_)
(fact 'sqrt-of-sq 't_)
(fact 'sqrt-of-sq 's_)
(fact 'rr-abs-of-nonneg 's_)
(have! '(AND (IN t_ RR) (IN t_ RR)))
(fact 'rr-mul-closed 't_ 't_)
(have! '(AND (IN s_ RR) (IN s_ RR)))
(fact 'rr-mul-closed 's_ 's_)
(fact 'rr-sq-nonneg 't_)
(fact 'rr-sq-nonneg 's_)
(have! '(AND (IN (* t_ t_) RR) (<= 0 (* t_ t_))))
(fact 'sqrt-nonneg '(* t_ t_))
(ai '(AND (IN (SQRT (* t_ t_)) RR) (<= 0 (SQRT (* t_ t_)))))
(have! '(AND (IN (* s_ s_) RR) (<= 0 (* s_ s_))))
(fact 'sqrt-nonneg '(* s_ s_))
(ai '(AND (IN (SQRT (* s_ s_)) RR) (<= 0 (SQRT (* s_ s_)))))
(have! '(AND (IN (* s_ s_) RR) (<= (* t_ t_) (* s_ s_))))
(fact 'sqrt-mono '(* t_ t_) '(* s_ s_))
(cm-ineq!)
(qed 'rr-le-of-sq-le)
(topic! 'rr-le-of-sq-le 'inequalities)


(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (IFF (= (magnitude z) 0) (= z 0))))))
(cm-peel!)
(let* ((w  (cm-coords! 'z))
       (cx (car w)) (cy (cadr w))
       (p  (cm-mag! 'z cx cy))
       (rt (list 'SQRT p))
       (mageq (list '= '(magnitude z) rt))
       (zeq   (list '= 'z (list '+ cx (list '* cy '+i)))))
  (fact 'cc-magnitude-closed 'z)
  (for-each
    (lambda (n)
      (dk-focus! n)
      ;; `di' is greedy: it may have peeled each direction's antecedent already,
      ;; so peel only if the leaf still shows an implication, and discriminate on
      ;; the GOAL rather than on the antecedent.
      (let ((g0 (dk-goal)))
        (if (and (pair? g0) (eq? (car g0) 'IMPLIES)) (di)))
      (let ((g (dk-goal)))
        (cond
          ((equal? g '(= z 0))
           ;; |z| = 0  =>  z = 0
           (fact 'sqrt-sq p)
           (fact 'eq-sym (list '* rt rt) p)
           (have! (list '= rt 0) (lambda () (cm-ineq!)))
           (have! (list '= p 0)
                  (lambda () (subst (list '= p (list '* rt rt)))
                             (subst (list '= rt 0))
                             (arith)))
           (have! (list '= (list '* cx cx) 0) (lambda () (cm-ineq!)))
           (have! (list '= (list '* cy cy) 0) (lambda () (cm-ineq!)))
           (fact 'rr-no-zero-divisors cx cx)
           (have! (list '= cx 0) (lambda () (cm-from-same-or! (list '= cx 0))))
           (fact 'rr-no-zero-divisors cy cy)
           (have! (list '= cy 0) (lambda () (cm-from-same-or! (list '= cy 0))))
           (subst zeq)
           (subst (list '= cx 0))
           (subst (list '= cy 0))
           (arith))
          (else
           ;; z = 0  =>  |z| = 0
           (fact 'rr-zero-in)
           (have! '(= z (+ 0 (* 0 +i))) (lambda () (subst '(= z 0)) (arith)))
           (fact 'cc-re-im-of 'z 0 0)
           (ai '(AND (= (real-part z) 0) (= (imag-part z) 0)))
           (have! (list '= cx 0) (lambda () (cm-ineq!)))
           (have! (list '= cy 0) (lambda () (cm-ineq!)))
           (fact 'sqrt-zero)
           (subst mageq)
           (subst (list '= cx 0))
           (subst (list '= cy 0))
           (have! '(= (+ (* 0 0) (* 0 0)) 0) (lambda () (arith)))
           (subst '(= (+ (* 0 0) (* 0 0)) 0))
           (ass)))))
    (dk-opened (lambda () (di)))))
(qed 'cc-magnitude-zero-iff)
(topic! 'cc-magnitude-zero-iff 'algebra)

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (= (magnitude (- z)) (magnitude z))))))
(cm-peel!)
(let* ((w  (cm-coords! 'z))
       (cx (car w)) (cy (cadr w))
       (p  (cm-mag! 'z cx cy))
       (zeq   (list '= 'z (list '+ cx (list '* cy '+i))))
       (mcx (list '- cx)) (mcy (list '- cy))
       (mageq (list '= '(magnitude z) (list 'SQRT p))))
  (fact 'rr-subset-cc cx)
  (fact 'rr-subset-cc cy)
  (fact 'cc-neg-closed 'z)
  (fact 'rr-neg-closed cx)
  (fact 'rr-neg-closed cy)
  (have! (list '= '(- z) (list '+ mcx (list '* mcy '+i)))
         (lambda () (subst zeq) (crs)))
  (fact 'cc-re-im-of '(- z) mcx mcy)
  (ai (list 'AND (list '= '(real-part (- z)) mcx) (list '= '(imag-part (- z)) mcy)))
  (let* ((p2 (cm-mag! '(- z) mcx mcy))
         (mageq2 (list '= '(magnitude (- z)) (list 'SQRT p2))))
    (subst mageq2)
    (subst mageq)
    (have! (list '= p2 p) (lambda () (crs)))
    (subst (list '= p2 p))
    (rfl)))
(qed 'cc-magnitude-neg)
(topic! 'cc-magnitude-neg 'algebra)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (= (magnitude a) (abs a))))))
(cm-peel!)
(fact 'rr-subset-cc 'a)
(fact 'rr-zero-in)
(have! '(= a (+ a (* 0 +i))) (lambda () (crs)))
(fact 'cc-re-im-of 'a 'a 0)
(ai '(AND (= (real-part a) a) (= (imag-part a) 0)))
(let* ((p (cm-mag! 'a 'a 0))
       (mageq (list '= '(magnitude a) (list 'SQRT p))))
  (fact 'sqrt-of-sq 'a)
  (subst mageq)
  (have! (list '= p '(* a a)) (lambda () (crs)))
  (subst (list '= p '(* a a)))
  (ass))
(qed 'rr-magnitude-is-abs)
(topic! 'rr-magnitude-is-abs 'algebra)

(sp (make-wff '(FORALL a (FORALL b (IMPLIES (AND (IN a CC) (IN b CC))
      (= (magnitude (* a b)) (* (magnitude a) (magnitude b))))))))
(cm-peel!)
(cm-split!)
(have! '(AND (IN a CC) (IN b CC)))
(fact 'cc-mul-closed 'a 'b)
(let* ((wa (cm-coords! 'a)) (cx (car wa)) (cy (cadr wa))
       (wb (cm-coords! 'b)) (cu (car wb)) (cv (cadr wb))
       (aeq (list '= 'a (list '+ cx (list '* cy '+i))))
       (beq (list '= 'b (list '+ cu (list '* cv '+i))))
       (c1  (list '- (list '* cx cu) (list '* cy cv)))
       (c2  (list '+ (list '* cx cv) (list '* cy cu))))
  (fact 'rr-subset-cc cx) (fact 'rr-subset-cc cy)
  (fact 'rr-subset-cc cu) (fact 'rr-subset-cc cv)
  ;; the coordinates of the product, typed in RR
  (have! (list 'AND (list 'IN cx 'RR) (list 'IN cu 'RR)))
  (fact 'rr-mul-closed cx cu)
  (have! (list 'AND (list 'IN cy 'RR) (list 'IN cv 'RR)))
  (fact 'rr-mul-closed cy cv)
  (have! (list 'AND (list 'IN cx 'RR) (list 'IN cv 'RR)))
  (fact 'rr-mul-closed cx cv)
  (have! (list 'AND (list 'IN cy 'RR) (list 'IN cu 'RR)))
  (fact 'rr-mul-closed cy cu)
  (fact 'rr-sub-in-rr (list '* cx cu) (list '* cy cv))
  (have! (list 'AND (list 'IN (list '* cx cv) 'RR) (list 'IN (list '* cy cu) 'RR)))
  (fact 'rr-add-closed (list '* cx cv) (list '* cy cu))
  ;; ab = c1 + c2 i
  (have! (list '= '(* a b) (list '+ c1 (list '* c2 '+i)))
         (lambda () (subst aeq) (subst beq) (crs)))
  (fact 'cc-re-im-of '(* a b) c1 c2)
  (ai (list 'AND (list '= '(real-part (* a b)) c1) (list '= '(imag-part (* a b)) c2)))
  (let* ((pa  (cm-mag! 'a cx cy))
         (pb  (cm-mag! 'b cu cv))
         (pab (cm-mag! '(* a b) c1 c2)))
    (fact 'sqrt-mul pa pb)
    (have! (list '= pab (list '* pa pb)) (lambda () (crs)))
    (subst (list '= '(magnitude (* a b)) (list 'SQRT pab)))
    (subst (list '= '(magnitude a) (list 'SQRT pa)))
    (subst (list '= '(magnitude b) (list 'SQRT pb)))
    (subst (list '= pab (list '* pa pb)))
    (ass)))
(qed 'cc-magnitude-mul)
(topic! 'cc-magnitude-mul 'algebra)


(sp (make-wff '(FORALL a (FORALL b (IMPLIES (AND (IN a CC) (IN b CC))
      (<= (magnitude (+ a b)) (+ (magnitude a) (magnitude b))))))))
(cm-peel!)
(cm-split!)
(have! '(AND (IN a CC) (IN b CC)))
(fact 'cc-add-closed 'a 'b)
(let* ((wa (cm-coords! 'a)) (cx (car wa)) (cy (cadr wa))
       (wb (cm-coords! 'b)) (cu (car wb)) (cv (cadr wb))
       (aeq (list '= 'a (list '+ cx (list '* cy '+i))))
       (beq (list '= 'b (list '+ cu (list '* cv '+i))))
       (sx  (list '+ cx cu))
       (sy  (list '+ cy cv)))
  (fact 'rr-subset-cc cx) (fact 'rr-subset-cc cy)
  (fact 'rr-subset-cc cu) (fact 'rr-subset-cc cv)
  (have! (list 'AND (list 'IN cx 'RR) (list 'IN cu 'RR)))
  (fact 'rr-add-closed cx cu)
  (have! (list 'AND (list 'IN cy 'RR) (list 'IN cv 'RR)))
  (fact 'rr-add-closed cy cv)
  (have! (list '= '(+ a b) (list '+ sx (list '* sy '+i)))
         (lambda () (subst aeq) (subst beq) (crs)))
  (fact 'cc-re-im-of '(+ a b) sx sy)
  (ai (list 'AND (list '= '(real-part (+ a b)) sx) (list '= '(imag-part (+ a b)) sy)))
  (let* ((pa (cm-mag! 'a cx cy))
         (pb (cm-mag! 'b cu cv))
         (ps (cm-mag! '(+ a b) sx sy))
         (aa (list 'SQRT pa)) (bb (list 'SQRT pb))
         (ab (list '* aa bb))
         (apb (list '+ aa bb))
         (apb2 (list '* apb apb))
         (tt (list '+ (list '* cx cu) (list '* cy cv)))
         (dd (list '- (list '* cx cv) (list '* cy cu))))
    (fact 'cc-magnitude-closed 'a)
    (fact 'cc-magnitude-closed 'b)
    (fact 'cc-magnitude-closed '(+ a b))
    ;; the four cross products, t and d
    ;; the two AND typings are already in context (rr-add-closed used them above)
    (fact 'rr-mul-closed cx cu)
    (fact 'rr-mul-closed cy cv)
    (have! (list 'AND (list 'IN cx 'RR) (list 'IN cv 'RR)))
    (fact 'rr-mul-closed cx cv)
    (have! (list 'AND (list 'IN cy 'RR) (list 'IN cu 'RR)))
    (fact 'rr-mul-closed cy cu)
    (have! (list 'AND (list 'IN (list '* cx cu) 'RR) (list 'IN (list '* cy cv) 'RR)))
    (fact 'rr-add-closed (list '* cx cu) (list '* cy cv))
    (fact 'rr-sub-in-rr (list '* cx cv) (list '* cy cu))
    (have! (list 'AND (list 'IN tt 'RR) (list 'IN tt 'RR)))
    (fact 'rr-mul-closed tt tt)
    (have! (list 'AND (list 'IN dd 'RR) (list 'IN dd 'RR)))
    (fact 'rr-mul-closed dd dd)
    (fact 'rr-sq-nonneg dd)
    ;; Cauchy-Schwarz in two dimensions: pa*pb - t^2 = d^2
    (have! (list 'AND (list 'IN pa 'RR) (list 'IN pb 'RR)))
    (fact 'rr-mul-closed pa pb)
    (have! (list '= (list '* pa pb) (list '+ (list '* tt tt) (list '* dd dd)))
           (lambda () (crs)))
    (have! (list '<= (list '* tt tt) (list '* pa pb)) (lambda () (cm-ineq!)))
    ;; (A*B)^2 = pa*pb, and A*B >= 0
    (have! (list 'AND (list 'IN aa 'RR) (list 'IN bb 'RR)))
    (fact 'rr-mul-closed aa bb)
    (have! (list 'AND (list '<= 0 aa) (list '<= 0 bb)))
    (fact 'rr-leq-mul-nonneg aa bb)
    (have! (list 'AND (list 'IN ab 'RR) (list 'IN ab 'RR)))
    (fact 'rr-mul-closed ab ab)
    (have! (list 'AND (list 'IN aa 'RR) (list 'IN aa 'RR)))
    (fact 'rr-mul-closed aa aa)
    (have! (list 'AND (list 'IN bb 'RR) (list 'IN bb 'RR)))
    (fact 'rr-mul-closed bb bb)
    (fact 'sqrt-sq pa)
    (fact 'sqrt-sq pb)
    (have! (list '= (list '* ab ab) (list '* (list '* aa aa) (list '* bb bb)))
           (lambda () (crs)))
    (have! (list '= (list '* ab ab) (list '* pa pb))
           (lambda ()
             (subst (list '= (list '* ab ab) (list '* (list '* aa aa) (list '* bb bb))))
             (subst (list '= (list '* aa aa) pa))
             (subst (list '= (list '* bb bb) pb))
             (rfl)))
    (have! (list '<= (list '* tt tt) (list '* ab ab)) (lambda () (cm-ineq!)))
    (fact 'rr-le-of-sq-le tt ab)
    ;; the square bound, then sqrt-mono
    (fact 'rr-add-closed aa bb)
    (have! (list 'AND (list 'IN apb 'RR) (list 'IN apb 'RR)))
    (fact 'rr-mul-closed apb apb)
    (fact 'rr-sq-nonneg apb)
    (have! (list '= apb2 (list '+ (list '+ (list '* aa aa) (list '* bb bb))
                                  (list '* 2 ab)))
           (lambda () (crs)))
    (have! (list '= ps (list '+ (list '+ pa pb) (list '* 2 tt))) (lambda () (crs)))
    (have! (list '<= ps apb2) (lambda () (cm-ineq!)))
    (have! (list 'AND (list 'IN apb2 'RR) (list '<= 0 apb2)))
    (fact 'sqrt-nonneg apb2)
    (ai (list 'AND (list 'IN (list 'SQRT apb2) 'RR) (list '<= 0 (list 'SQRT apb2))))
    (have! (list 'AND (list 'IN apb2 'RR) (list '<= ps apb2)))
    (fact 'sqrt-mono ps apb2)
    (fact 'sqrt-of-sq apb)
    (have! (list '<= 0 apb) (lambda () (cm-ineq!)))
    (fact 'rr-abs-of-nonneg apb)
    (cm-ineq!)))
(qed 'cc-magnitude-triangle)
(topic! 'cc-magnitude-triangle 'inequalities)

