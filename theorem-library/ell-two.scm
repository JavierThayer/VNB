;;; ell-two.scm -- ELL-TWO, the square-summable complex sequences, and the
;;; closure of that carrier under the pointwise vector operations.
;;;
;;; WHY THIS FILE EXISTS.  `cips-schwarz' (Cauchy-Schwarz) and `cips-minkowski'
;;; are PROVEN `modulo 0' (theorem-library/inner-product-inequalities.scm), and
;;; COMPLEX-INNER-PRODUCT-SPACE has NO INSTANCE -- it is one of the thirteen
;;; entries of `structure-exemplification-audit's UNWITNESSED list.  A theorem
;;; about a structure nothing satisfies is true and empty.  l^2(NN; CC) is the
;;; witness that makes those two inequalities say something, and this file is
;;; its first storey: the carrier, the proof that the carrier is INHABITED, and
;;; three of the four closure facts a vector-space structure needs before it can
;;; be declared -- the zero, the pointwise sum and the pointwise negation.
;;;
;;; THE FOURTH, closure under the scalar action, is NOT here and is left for
;;; the user: prove-scripts/drives/ell-two-act-closed-drive.scm.  It is blocked
;;; on one real-series lemma the tree does not have -- a convergent nonnegative
;;; series stays convergent under a nonnegative constant scale -- and that
;;; lemma is an induction whose statement is not ni-shaped, which is exactly
;;; what `what-now's induction lane exists to name.  The drive says so.
;;;
;;; WHAT IS DELIBERATELY NOT HERE, and why.  The INNER PRODUCT
;;; <x,y> = Sum_k x(k) conj(y(k)) is a COMPLEX series, and the tree has none:
;;; SERIES-PARTIAL-SUM (theorem-library/power-series.scm) is hard-wired to
;;; NORMED-FIELD-ADDITIVE-AG(RR-NORMED-FIELD) and SERIES-CONVERGES / -TO to
;;; RR-MS.  So no `declare-instance!' happens in this file; see the measurement
;;; in the session note.  The CARRIER, by contrast, needs no complex series at
;;; all -- |x(k)|^2 is REAL -- which is exactly why this storey is reachable
;;; today and why it is the same carrier whatever the complex-series layer
;;; eventually looks like.  ELL-ONE (dominated-convergence.scm:1428) is built
;;; on the same observation.
;;;
;;; THE SQUARE IS WRITTEN AS A PRODUCT, `magnitude(x)*magnitude(x)', not as
;;; `power(magnitude(x), 2)' and not with RPOW.  RPOW is axiomatic and
;;; RATIONAL-exponent only, so l^p for a general real p is out of reach; l^2
;;; wants only SQRT (for the norm, later) and l^1 no root at all.  The product
;;; form is also what `crs' and `ineq' read: a product of two atoms is an ATOM
;;; the oracle can certify, where a POWER is not.
;;;
;;; Dependencies: dominated-convergence (series-converges-sum, and the ELL-ONE
;;; idiom this file copies), comparison-test-proof (comparison-test),
;;; cc-magnitude (cc-magnitude-closed/-nonneg/-triangle/-mul), rr-order-basics
;;; (rr-sq-nonneg, rr-prod-le-prod), sqn (SQN, sqn-membership, sqn-sethood),
;;; power-series (SERIES-CONVERGES), driver-kit.

;;; ---- file-local driver helpers (the `e2-' prefix) --------------------

(define (e2-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "e2-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (e2-ineq . forms) (apply ineq (map e2-idx forms)))

;;; `di' until an ASSUMPTION lands.  An UNGUARDED universal peels the
;;; quantifier and lands nothing, so loop on the LANDING, never on a `di' count.
(define (e2-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "e2-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (e2-di-landed-1!)
  (let ((new (e2-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "e2-di-landed-1!: expected 1" (map expression->string new)))))

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (e2-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "e2-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (e2-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (e2-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; =====================================================================
;;; L1.  (u+v)^2 <= 2u^2 + 2v^2, for ALL reals -- no nonnegativity needed,
;;; the slack being (u-v)^2.  Written with doubling rather than the literal 2
;;; so `crs' never meets a numeral, and so the shape matches the `a + a'
;;; idiom `series-converges-sum' is applied through below.
;;; =====================================================================

(sp (make-wff "forall([u in rr, v in rr],
     (u + v) * (u + v) <= ((u * u) + (u * u)) + ((v * v) + (v * v)))"))
(e2-di-landed!)
(have! '(AND (IN u RR) (IN v RR)))
(fact 'rr-add-closed 'u 'v)
(fact 'rr-sub-in-rr 'u 'v)
(have! '(AND (IN (+ u v) RR) (IN (+ u v) RR)))
(fact 'rr-mul-closed '(+ u v) '(+ u v))
(have! '(AND (IN (- u v) RR) (IN (- u v) RR)))
(fact 'rr-mul-closed '(- u v) '(- u v))
(have! '(AND (IN u RR) (IN u RR)))
(fact 'rr-mul-closed 'u 'u)
(have! '(AND (IN v RR) (IN v RR)))
(fact 'rr-mul-closed 'v 'v)
(fact 'rr-sq-nonneg '(- u v))
(have! '(= (+ (* (+ u v) (+ u v)) (* (- u v) (- u v)))
           (+ (+ (* u u) (* u u)) (+ (* v v) (* v v))))
  (lambda () (crs)))
(e2-ineq '(= (+ (* (+ u v) (+ u v)) (* (- u v) (- u v)))
             (+ (+ (* u u) (* u u)) (+ (* v v) (* v v))))
         '(<= 0 (* (- u v) (- u v))))
(qed 'rr-sq-add-le)
(topic! 'rr-sq-add-le 'inequalities)
(alias! 'rr-sq-add-le "the square of a sum is at most twice the sum of the squares")

;;; =====================================================================
;;; L2.  The same at CC: |p+q|^2 <= 2|p|^2 + 2|q|^2.  This is the
;;; termwise estimate the whole closure argument rests on, and it is why
;;; the dominating series below is (F+F)+(G+G) and nothing smaller.
;;; =====================================================================

(sp (make-wff "forall([p_ in cc, q_ in cc],
     magnitude(p_ + q_) * magnitude(p_ + q_) <=
       ((magnitude(p_) * magnitude(p_)) + (magnitude(p_) * magnitude(p_))) +
       ((magnitude(q_) * magnitude(q_)) + (magnitude(q_) * magnitude(q_))))"))
(e2-di-landed!)
(have! '(AND (IN p_ CC) (IN q_ CC)))
(fact 'cc-add-closed 'p_ 'q_)
(fact 'cc-magnitude-closed 'p_)
(fact 'cc-magnitude-closed 'q_)
(fact 'cc-magnitude-closed '(+ p_ q_))
(fact 'cc-magnitude-nonneg '(+ p_ q_))
(fact 'cc-magnitude-triangle 'p_ 'q_)
(have! '(AND (IN (magnitude p_) RR) (IN (magnitude q_) RR)))
(fact 'rr-add-closed '(magnitude p_) '(magnitude q_))
(have! '(AND (IN (magnitude (+ p_ q_)) RR) (IN (magnitude (+ p_ q_)) RR)))
(fact 'rr-mul-closed '(magnitude (+ p_ q_)) '(magnitude (+ p_ q_)))
(have! '(AND (IN (+ (magnitude p_) (magnitude q_)) RR)
             (IN (+ (magnitude p_) (magnitude q_)) RR)))
(fact 'rr-mul-closed '(+ (magnitude p_) (magnitude q_))
                     '(+ (magnitude p_) (magnitude q_)))
(have! '(AND (IN (magnitude p_) RR) (IN (magnitude p_) RR)))
(fact 'rr-mul-closed '(magnitude p_) '(magnitude p_))
(have! '(AND (IN (magnitude q_) RR) (IN (magnitude q_) RR)))
(fact 'rr-mul-closed '(magnitude q_) '(magnitude q_))
;; Squaring is monotone on the nonnegatives -- `rr-prod-le-prod' with both
;; factors equal.  This is the step `ineq' cannot take: a product of two
;; variables is not linear.
(have! '(AND (AND (<= 0 (magnitude (+ p_ q_)))
                  (<= (magnitude (+ p_ q_)) (+ (magnitude p_) (magnitude q_))))
             (AND (<= 0 (magnitude (+ p_ q_)))
                  (<= (magnitude (+ p_ q_)) (+ (magnitude p_) (magnitude q_))))))
;; Both bounds are READ BACK off their own landings rather than rebuilt: the
;; parser flattens `+' and re-folds it to the LEFT, so a hand-built
;; ((A+A)+(B+B)) is NOT the ((A+A)+B)+B that is actually in the context, and
;; `ineq's index lookup would miss it.
(define e2-pl (dk-fact! 'rr-prod-le-prod
                        '(magnitude (+ p_ q_)) '(+ (magnitude p_) (magnitude q_))
                        '(magnitude (+ p_ q_)) '(+ (magnitude p_) (magnitude q_))))
(define e2-sq (dk-fact! 'rr-sq-add-le '(magnitude p_) '(magnitude q_)))
(apply ineq (map e2-idx (list e2-pl e2-sq)))
(qed 'cc-magnitude-sq-add-le)
(topic! 'cc-magnitude-sq-add-le 'inequalities)
(alias! 'cc-magnitude-sq-add-le
        "the squared magnitude of a sum is at most twice the sum of the squared magnitudes")

;;; =====================================================================
;;; ELL-TWO, and its membership characterisation.  Exactly the ELL-ONE
;;; idiom (dominated-convergence.scm:1428): a SEP over SQN(CC), whose
;;; sethood comes from `sqn-sethood' + `cc-is-set', and a membership IFF
;;; PROVEN from the definition by `sep-me' / `sep-mi'.
;;; =====================================================================

(def-constant 'ELL-TWO
  '(ell-two-def
    (= ELL-TWO
       (SEP x_ (SQN CC)
            (SERIES-CONVERGES
              (VNB-LAMBDA k_ NN (* (magnitude (x_ k_)) (magnitude (x_ k_)))))))))
(notation! 'ELL-TWO 'kind 'constant 'arity 0
           'english "the square-summable complex sequences"
           'tex "\\ell^2")

(sp (make-wff "forall([y_], y_ in ell-two iff
     (y_ in sqn(cc) and
      series-converges(vnb-lambda(k_, nn, magnitude(y_(k_)) * magnitude(y_(k_))))))"))
(mac 'ell-two-def)
(define e2-sep '(SEP x_ (SQN CC)
                  (SERIES-CONVERGES
                    (VNB-LAMBDA k_ NN (* (magnitude (x_ k_)) (magnitude (x_ k_)))))))
(fact 'cc-is-set)
(fact 'sqn-sethood 'CC)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'AND)
       ;; forward: separation ELIMINATION splits the membership
       (begin (sep-me (list 'IN 'y_ e2-sep))
              (e2-and! (lambda () (ass))))
       ;; backward: separation INTRODUCTION, from the two conjuncts
       (begin (dk-split! (e2-find 'conj (dk-head? 'AND)))
              (for-each (lambda (k) (dk-focus! k) (ass))
                        (dk-opened (lambda () (sep-mi)))))))
 (dk-opened (lambda () (di) (di))))
(qed 'ell-two-membership)
(topic! 'ell-two-membership 'analysis)
(alias! 'ell-two-membership "membership in ell^2")

;;; =====================================================================
;;; CLOSURE UNDER THE POINTWISE SUM -- the first theorem with content.
;;;
;;; It is NOT free, and the reason is the whole shape of the argument: the
;;; termwise estimate |x+y|^2 <= 2|x|^2 + 2|y|^2 (L2) needs a DOMINATING
;;; series, and the smallest one available is (F+F)+(G+G) where F, G are the
;;; two squared-magnitude series.  `series-converges-sum' assembles it in
;;; three applications -- F+F, G+G, then their sum -- exactly the `a + a'
;;; idiom dominated-convergence.scm uses for the same reason, and the
;;; comparison test closes it.
;;;
;;; TRANSFER FORM: the conclusion is about any `z_' agreeing pointwise with
;;; the sum, not about the literal lambda.  Same reason as rr-null-sum and
;;; series-converges-sum: a conclusion about the literal lambda would need a
;;; beta under a binder at every application site, and the structure
;;; declaration that will eventually consume this wants the transfer form.
;;; =====================================================================

;;; beta-reduce the GOAL to exhaustion (one `lam-b' takes siblings, not nests)
(define (e2-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred e2-has-redex? e))))
(define (e2-beta!)
  (let lp ((n 0))
    (if (and (< n 6) (e2-has-redex? (dk-goal)))
        (begin (lam-b) (lp (+ n 1))))))

;;; (IN F (FUN NN RR)) for F = k |-> |s(k)|^2, s : NN -> CC.
(define (e2-sq-fun! F s)
  (have! (list 'IN F '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let* ((k  (cadr (e2-di-landed-1!)))
             (sk (list s k))
             (m  (list 'magnitude sk)))
        (fact 'fun-apply-type-c s 'NN 'CC k)
        (fact 'cc-magnitude-closed sk)
        (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
        (fact 'rr-mul-closed m m)
        (ass)))))

;;; forall k in NN.  0 <= |s(k)|^2.
(define (e2-sq-nonneg! F s)
  (have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list '<= 0 (list F 'n_))))
    (lambda ()
      (let* ((k  (cadr (e2-di-landed-1!)))
             (sk (list s k))
             (m  (list 'magnitude sk)))
        (e2-beta!)
        (fact 'fun-apply-type-c s 'NN 'CC k)
        (fact 'cc-magnitude-closed sk)
        (fact 'rr-sq-nonneg m)
        (ass)))))

(sp (make-wff "forall([x_ in ell-two, y_ in ell-two, z_ in sqn(cc)],
     forall([k_ in nn], z_(k_) = x_(k_) + y_(k_)) implies z_ in ell-two)"))
;; `di' is greedy but not exhaustive: the three guarded typings land on one
;; call and the pointwise ANTECEDENT only on the next, so peel until the goal
;; is the bare membership.
(let lp ()
  (if (memq (car (dk-goal)) '(FORALL IMPLIES)) (begin (e2-di-landed!) (lp))))
(define e2a-pw (e2-find 'pointwise
                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'z_)
                                  (dk-contains? a '=)))))
;; unfold the two hypotheses and the codomain of z_
(dk-split! (dk-landed-find (lambda () (mac-h 'ell-two-membership '(IN x_ ELL-TWO)))
                           (lambda (a) (eq? (car a) 'AND))))
(dk-split! (dk-landed-find (lambda () (mac-h 'ell-two-membership '(IN y_ ELL-TWO)))
                           (lambda (a) (eq? (car a) 'AND))))
(mac-h 'sqn-membership '(IN x_ (SQN CC)))
(mac-h 'sqn-membership '(IN y_ (SQN CC)))
(mac-h 'sqn-membership '(IN z_ (SQN CC)))

(define e2a-fx '(VNB-LAMBDA k_ NN (* (magnitude (x_ k_)) (magnitude (x_ k_)))))
(define e2a-fy '(VNB-LAMBDA k_ NN (* (magnitude (y_ k_)) (magnitude (y_ k_)))))
(define e2a-fz '(VNB-LAMBDA k_ NN (* (magnitude (z_ k_)) (magnitude (z_ k_)))))
(define e2a-ax '(VNB-LAMBDA k_ NN (+ (* (magnitude (x_ k_)) (magnitude (x_ k_)))
                                     (* (magnitude (x_ k_)) (magnitude (x_ k_))))))
(define e2a-ay '(VNB-LAMBDA k_ NN (+ (* (magnitude (y_ k_)) (magnitude (y_ k_)))
                                     (* (magnitude (y_ k_)) (magnitude (y_ k_))))))
(define e2a-c  '(VNB-LAMBDA k_ NN
                  (+ (+ (* (magnitude (x_ k_)) (magnitude (x_ k_)))
                        (* (magnitude (x_ k_)) (magnitude (x_ k_))))
                     (+ (* (magnitude (y_ k_)) (magnitude (y_ k_)))
                        (* (magnitude (y_ k_)) (magnitude (y_ k_)))))))

(e2-sq-fun! e2a-fx 'x_)
(e2-sq-fun! e2a-fy 'y_)
(e2-sq-fun! e2a-fz 'z_)
(e2-sq-nonneg! e2a-fx 'x_)
(e2-sq-nonneg! e2a-fy 'y_)

;;; the doubled series (F+F) and (G+G) and their sum, with the three
;;; typings, three nonnegativities and three pointwise equations
;;; `series-converges-sum' asks for.
(define (e2a-double! A F s)
  ;; F's own typing and nonnegativity are landed by the caller: `have!' of a
  ;; claim ALREADY in context up to alpha is a self-loop, not a no-op.
  (have! (list 'IN A '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let* ((k  (cadr (e2-di-landed-1!)))
             (sk (list s k))
             (m  (list 'magnitude sk))
             (mm (list '* m m)))
        (fact 'fun-apply-type-c s 'NN 'CC k)
        (fact 'cc-magnitude-closed sk)
        (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
        (fact 'rr-mul-closed m m)
        (have! (list 'AND (list 'IN mm 'RR) (list 'IN mm 'RR)))
        (fact 'rr-add-closed mm mm)
        (ass))))
  ;; `rfl' carries a DEFINEDNESS guard -- `=' is partial, so t = t is a
  ;; CLAIM about t -- and neither side here is syntactically self-defined
  ;; (both are applications of `magnitude' to an application).  The typings
  ;; have to be in context BEFORE the rfl, not after it.
  (have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
            (list '= (list A 'n_) (list '+ (list F 'n_) (list F 'n_)))))
    (lambda ()
      (let* ((k  (cadr (e2-di-landed-1!)))
             (sk (list s k))
             (m  (list 'magnitude sk))
             (mm (list '* m m)))
        (e2-beta!)
        (fact 'fun-apply-type-c s 'NN 'CC k)
        (fact 'cc-magnitude-closed sk)
        (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
        (fact 'rr-mul-closed m m)
        (have! (list 'AND (list 'IN mm 'RR) (list 'IN mm 'RR)))
        (fact 'rr-add-closed mm mm)
        (rfl))))
  ;; `ineq' demands an (IN _ RR) certificate for EVERY atom it sees, and the
  ;; atoms here are m*m and its double -- not just m.
  (have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list '<= 0 (list A 'n_))))
    (lambda ()
      (let* ((k  (cadr (e2-di-landed-1!)))
             (sk (list s k))
             (m  (list 'magnitude sk))
             (mm (list '* m m)))
        (e2-beta!)
        (fact 'fun-apply-type-c s 'NN 'CC k)
        (fact 'cc-magnitude-closed sk)
        (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
        (fact 'rr-mul-closed m m)
        (have! (list 'AND (list 'IN mm 'RR) (list 'IN mm 'RR)))
        (fact 'rr-add-closed mm mm)
        (fact 'rr-sq-nonneg m)
        (e2-ineq (list '<= 0 mm)))))
  (dk-fact! 'series-converges-sum F F A))

(e2a-double! e2a-ax e2a-fx 'x_)
(e2a-double! e2a-ay e2a-fy 'y_)

;;; ... and C = A + B.
(have! (list 'IN e2a-c '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((k (cadr (e2-di-landed-1!))))
      (for-each
       (lambda (s)
         (let* ((sk (list s k)) (m (list 'magnitude sk)) (mm (list '* m m)))
           (fact 'fun-apply-type-c s 'NN 'CC k)
           (fact 'cc-magnitude-closed sk)
           (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
           (fact 'rr-mul-closed m m)
           (have! (list 'AND (list 'IN mm 'RR) (list 'IN mm 'RR)))
           (fact 'rr-add-closed mm mm)))
       '(x_ y_))
      (let ((ax (list '+ (list '* (list 'magnitude (list 'x_ k)) (list 'magnitude (list 'x_ k)))
                            (list '* (list 'magnitude (list 'x_ k)) (list 'magnitude (list 'x_ k)))))
            (ay (list '+ (list '* (list 'magnitude (list 'y_ k)) (list 'magnitude (list 'y_ k)))
                            (list '* (list 'magnitude (list 'y_ k)) (list 'magnitude (list 'y_ k))))))
        (have! (list 'AND (list 'IN ax 'RR) (list 'IN ay 'RR)))
        (fact 'rr-add-closed ax ay)
        (ass)))))
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list '= (list e2a-c 'n_) (list '+ (list e2a-ax 'n_) (list e2a-ay 'n_)))))
  (lambda ()
    (let ((k (cadr (e2-di-landed-1!))))
      (e2-beta!)
      (let ((doubles
             (map (lambda (s)
                    (let* ((sk (list s k)) (m (list 'magnitude sk)) (mm (list '* m m)))
                      (fact 'fun-apply-type-c s 'NN 'CC k)
                      (fact 'cc-magnitude-closed sk)
                      (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
                      (fact 'rr-mul-closed m m)
                      (have! (list 'AND (list 'IN mm 'RR) (list 'IN mm 'RR)))
                      (fact 'rr-add-closed mm mm)
                      (list '+ mm mm)))
                  '(x_ y_))))
        (have! (list 'AND (list 'IN (car doubles) 'RR) (list 'IN (cadr doubles) 'RR)))
        (fact 'rr-add-closed (car doubles) (cadr doubles)))
      (rfl))))
(dk-fact! 'series-converges-sum e2a-ax e2a-ay e2a-c)

;;; the termwise estimate, and the comparison test.
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'AND (list '<= 0 (list e2a-fz 'n_))
                     (list '<= (list e2a-fz 'n_) (list e2a-c 'n_)))))
  (lambda ()
    (let* ((k  (cadr (e2-di-landed-1!)))
           (xk (list 'x_ k)) (yk (list 'y_ k)) (zk (list 'z_ k))
           (sk (list '+ xk yk)))
      (e2-beta!)
      (inst+ e2a-pw k)
      (fact 'fun-apply-type-c 'x_ 'NN 'CC k)
      (fact 'fun-apply-type-c 'y_ 'NN 'CC k)
      (fact 'fun-apply-type-c 'z_ 'NN 'CC k)
      (subst (list '= zk sk))
      (have! (list 'AND (list 'IN xk 'CC) (list 'IN yk 'CC)))
      (fact 'cc-add-closed xk yk)
      (fact 'cc-magnitude-closed xk)
      (fact 'cc-magnitude-closed yk)
      (fact 'cc-magnitude-closed sk)
      (for-each (lambda (m)
                  (have! (list 'AND (list 'IN m 'RR) (list 'IN m 'RR)))
                  (fact 'rr-mul-closed m m))
                (list (list 'magnitude xk) (list 'magnitude yk) (list 'magnitude sk)))
      (fact 'rr-sq-nonneg (list 'magnitude sk))
      (let ((bd (dk-fact! 'cc-magnitude-sq-add-le xk yk)))
        (e2-and!
         (lambda ()
           (if (equal? (cadr (dk-goal)) 0)
               (e2-ineq (list '<= 0 (list '* (list 'magnitude sk) (list 'magnitude sk))))
               (apply ineq (map e2-idx (list bd))))))))))
(have! (list 'AND
         (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                 (list 'AND (list '<= 0 (list e2a-fz 'n_))
                            (list '<= (list e2a-fz 'n_) (list e2a-c 'n_)))))
         (list 'SERIES-CONVERGES e2a-c)))
(dk-fact! 'comparison-test e2a-fz e2a-c)

(mac 'ell-two-membership)
;; `mac-h' REPLACED `z_ in sqn(cc)' with `z_ in fun(nn,cc)' above -- it is
;; destructive -- so the SQN conjunct of the goal is rewritten rather than
;; matched.
(e2-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN) (begin (mac 'sqn-membership) (ass)) (ass))))
(qed 'ell-two-add-closed)
(topic! 'ell-two-add-closed 'analysis)
(alias! 'ell-two-add-closed "ell^2 is closed under the pointwise sum")

;;; =====================================================================
;;; THE CARRIER IS NOT EMPTY.
;;;
;;; This is not a formality and it is the whole reason the file exists: a
;;; carrier nothing is ever shown to inhabit reproduces, one level down,
;;; exactly the defect that a structure predicate nothing satisfies is.  The
;;; zero sequence is the witness, and reaching it costs one induction --
;;; the partial sums of the zero series are all 0 -- plus
;;; `monotone-convergence-rr' with the bound 0.
;;; =====================================================================

(define e2z '(VNB-LAMBDA n_ NN 0))

(sp (make-wff (list 'IN e2z '(FUN NN RR))))
(fact 'rr-zero-in)
(dk-lam-t!)
(e2-di-landed-1!)
(ass)
(qed 'zero-seq-in-fun)
(topic! 'zero-seq-in-fun 'analysis)

(sp (make-wff (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                (list '= (list 'SERIES-PARTIAL-SUM e2z 'k_) 0)))))
(ni)
(for-each
 (lambda (l)
   (dk-focus! l)
   (let ((g (dk-goal)))
     (if (dk-contains? g 'succ)
         ;; step: S(Z, succ k) = S(Z,k) + Z(k) = 0 + 0
         (let ((k (cadr (e2-di-landed-1!))))
           (e2-di-landed!)                       ; the induction hypothesis
           (mac 'series-partial-sum-succ)
           (e2-beta!)
           (subst (list '= (list 'SERIES-PARTIAL-SUM e2z k) 0))
           (arith))
         ;; base: S(Z, 0) = 0
         (begin (mac 'series-partial-sum-zero) (arith)))))
 (proof-leaves))
(qed 'series-partial-sum-zero-seq)
(topic! 'series-partial-sum-zero-seq 'analysis)
(alias! 'series-partial-sum-zero-seq "every partial sum of the zero series is 0")

;;; The zero series converges.  `monotone-convergence-rr' with the bound 0:
;;; the partial sums are constant, so "nondecreasing" and "bounded above" are
;;; both the induction above read twice.
(define e2zs (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM e2z 'k)))

(sp (make-wff (list 'SERIES-CONVERGES e2z)))
(fact 'zero-seq-in-fun)
(fact 'series-partial-sum-seq-in-fun e2z)
(have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
          (list '<= (list e2zs 'k_) (list e2zs '(succ k_)))))
  (lambda ()
    (let ((k (cadr (e2-di-landed-1!))))
      (fact 'nn-succ-closed k)
      (mac 'series-partial-sum-seq-apply)
      (fact 'series-partial-sum-zero-seq k)
      (fact 'series-partial-sum-zero-seq (list 'succ k))
      (subst (list '= (list 'SERIES-PARTIAL-SUM e2z k) 0))
      (subst (list '= (list 'SERIES-PARTIAL-SUM e2z (list 'succ k)) 0))
      (arith))))
(fact 'rr-zero-in)
(have! (list 'FORSOME 'bnd (list 'AND '(IN bnd RR)
          (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list '<= (list e2zs 'k_) 'bnd)))))
  (lambda ()
    (ew 0)
    (e2-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN) (ass)
           (let ((k (cadr (e2-di-landed-1!))))
             (mac 'series-partial-sum-seq-apply)
             (fact 'series-partial-sum-zero-seq k)
             (subst (list '= (list 'SERIES-PARTIAL-SUM e2z k) 0))
             (arith)))))))
(have! (list 'AND
         (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                 (list '<= (list e2zs 'k_) (list e2zs '(succ k_)))))
         (list 'FORSOME 'bnd (list 'AND '(IN bnd RR)
                 (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                         (list '<= (list e2zs 'k_) 'bnd)))))))
(fact 'monotone-convergence-rr e2zs)
(mac 'series-converges)
(ass)
(qed 'zero-series-converges)
(topic! 'zero-series-converges 'analysis)
(alias! 'zero-series-converges "the zero series converges")

;;; ... and so ELL-TWO is INHABITED.
(sp (make-wff (list 'IN e2z 'ELL-TWO)))
(fact 'cc-zero-in)
(have! '(= (magnitude 0) 0)
  (lambda ()
    (fact 'cc-magnitude-zero-iff 0)
    (have! '(= 0 0) (lambda () (arith)))
    (prop)))
(fact 'cc-magnitude-closed 0)
(have! '(AND (IN (magnitude 0) RR) (IN (magnitude 0) RR)))
(fact 'rr-mul-closed '(magnitude 0) '(magnitude 0))
(fact 'zero-seq-in-fun)
(fact 'zero-series-converges)
(define e2zsq (list 'VNB-LAMBDA 'k_ 'NN
                (list '* (list 'magnitude (list e2z 'k_))
                         (list 'magnitude (list e2z 'k_)))))
(have! (list 'IN e2zsq '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (e2-di-landed-1!)
    (e2-beta!)
    (ass)))
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'AND (list '<= 0 (list e2zsq 'n_))
                     (list '<= (list e2zsq 'n_) (list e2z 'n_)))))
  (lambda ()
    (let ((k (cadr (e2-di-landed-1!))))
      (e2-beta!)
      (subst '(= (magnitude 0) 0))
      (e2-and! (lambda () (arith))))))
(have! (list 'AND
         (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                 (list 'AND (list '<= 0 (list e2zsq 'n_))
                            (list '<= (list e2zsq 'n_) (list e2z 'n_)))))
         (list 'SERIES-CONVERGES e2z)))
(dk-fact! 'comparison-test e2zsq e2z)
(mac 'ell-two-membership)
(e2-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN)
       (begin (mac 'sqn-membership) (dk-lam-t!) (e2-di-landed-1!) (ass))
       (ass))))
(qed 'ell-two-zero-in)
(topic! 'ell-two-zero-in 'analysis)
(alias! 'ell-two-zero-in "the zero sequence is square-summable")

;;; =====================================================================
;;; CLOSURE UNDER THE POINTWISE NEGATION.  Cheap, and worth stating for the
;;; contrast with the sum: |-w| = |w| (`cc-magnitude-neg'), so the
;;; squared-magnitude series of -x is POINTWISE EQUAL to that of x and the
;;; comparison test closes it against x's own series -- no dominator has to
;;; be built.
;;; =====================================================================

(sp (make-wff "forall([x_ in ell-two, z_ in sqn(cc)],
     forall([k_ in nn], z_(k_) = -(x_(k_))) implies z_ in ell-two)"))
(let lp ()
  (if (memq (car (dk-goal)) '(FORALL IMPLIES)) (begin (e2-di-landed!) (lp))))
(define e2n-pw (e2-find 'pointwise
                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'z_)
                                  (dk-contains? a '=)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'ell-two-membership '(IN x_ ELL-TWO)))
                           (lambda (a) (eq? (car a) 'AND))))
(mac-h 'sqn-membership '(IN x_ (SQN CC)))
(mac-h 'sqn-membership '(IN z_ (SQN CC)))
(define e2n-fx '(VNB-LAMBDA k_ NN (* (magnitude (x_ k_)) (magnitude (x_ k_)))))
(define e2n-fz '(VNB-LAMBDA k_ NN (* (magnitude (z_ k_)) (magnitude (z_ k_)))))
(e2-sq-fun! e2n-fx 'x_)
(e2-sq-fun! e2n-fz 'z_)
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'AND (list '<= 0 (list e2n-fz 'n_))
                     (list '<= (list e2n-fz 'n_) (list e2n-fx 'n_)))))
  (lambda ()
    (let* ((k  (cadr (e2-di-landed-1!)))
           (xk (list 'x_ k)) (zk (list 'z_ k)))
      (e2-beta!)
      (inst+ e2n-pw k)
      (fact 'fun-apply-type-c 'x_ 'NN 'CC k)
      (fact 'fun-apply-type-c 'z_ 'NN 'CC k)
      (subst (list '= zk (list '- xk)))
      (fact 'cc-magnitude-neg xk)
      (subst (list '= (list 'magnitude (list '- xk)) (list 'magnitude xk)))
      (fact 'cc-magnitude-closed xk)
      (fact 'rr-sq-nonneg (list 'magnitude xk))
      (have! (list 'AND (list 'IN (list 'magnitude xk) 'RR)
                        (list 'IN (list 'magnitude xk) 'RR)))
      (fact 'rr-mul-closed (list 'magnitude xk) (list 'magnitude xk))
      (fact 'rr-leq-reflexive (list '* (list 'magnitude xk) (list 'magnitude xk)))
      (e2-and! (lambda () (ass))))))
(have! (list 'AND
         (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                 (list 'AND (list '<= 0 (list e2n-fz 'n_))
                            (list '<= (list e2n-fz 'n_) (list e2n-fx 'n_)))))
         (list 'SERIES-CONVERGES e2n-fx)))
(dk-fact! 'comparison-test e2n-fz e2n-fx)
(mac 'ell-two-membership)
(e2-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN) (begin (mac 'sqn-membership) (ass)) (ass))))
(qed 'ell-two-neg-closed)
(topic! 'ell-two-neg-closed 'analysis)
(alias! 'ell-two-neg-closed "ell^2 is closed under the pointwise negation")
