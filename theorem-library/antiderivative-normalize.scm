;;; antiderivative-normalize.scm -- SHIFTING AN ANTIDERIVATIVE BY A CONSTANT,
;;; and the NORMALISED antiderivative family that docs/calculus.pdf Cor 4.17
;;; needs and that nothing in the tree supplied.
;;;
;;;   antiderivative-shift-const        IS-ANTIDERIVATIVE(f, phi, a, b), c in RR
;;;                                     =>  IS-ANTIDERIVATIVE(z |-> f(z) - c, phi, a, b)
;;;   antiderivable-family-normalized   forall k. IS-ANTIDERIVABLE(phifam(k),a,b)
;;;                                     =>  forsome fam. forall k.
;;;                                         IS-ANTIDERIVATIVE(fam(k), phifam(k), a, b)
;;;                                         and fam(k)(a) = 0
;;;
;;; WHY THE SECOND ONE EXISTS, which is the interesting half.  Prop 4.16 carries
;;; THREE hypotheses and the middle one -- "the sequence of real numbers f_k(a)
;;; is convergent" -- is not implied by the other two: the antiderivatives of a
;;; convergent sequence of integrands are determined only up to an additive
;;; constant, and nothing stops those constants from running away.  Cor 4.17
;;; ("the antiderivable functions are closed under uniform limits") has no such
;;; hypothesis to offer, and the standard repair is the one taken here: do not
;;; ASSUME the constants behave, CHOOSE them.  Normalising each antiderivative
;;; to vanish at a makes f_k(a) = 0 for every k, which is convergent for the
;;; cheapest of reasons.
;;;
;;; The normalisation is not free, and this is the gap: it needs
;;; `antiderivative-shift-const', i.e. that f - c is still an antiderivative of
;;; phi, which the tree did not have.  Prop 4.10
;;; (`antiderivative-differ-by-constant', antiderivative.scm) is the CONVERSE --
;;; two antiderivatives of the same function differ by a constant -- and does
;;; not give it.
;;;
;;; HOW THE SHIFT IS PROVED, and why not directly.  The obvious route unfolds
;;; Def 4.6 and re-proves its two clauses for `z |-> f(z) - c'.  It cannot use
;;; `sub-continuous-at' / `deriv-sub' when it gets there: those conclude about
;;; the LITERAL lambda `z |-> g(z) - h(z)', and with h the constant map that is
;;; `z |-> f(z) - (VNB-LAMBDA x. c)(z)', which is not the term wanted.  So a
;;; pointwise transfer is owed either way, and once it is owed the whole thing
;;; is three citations rather than a driver:
;;;
;;;   (1) the constant map is an antiderivative of the zero map on [a,b]
;;;       (`const-continuous-at' and `deriv-const', twelve lines);
;;;   (2) `antiderivative-sub' (Prop 4.8) subtracts it, giving the antiderivative
;;;       `z |-> f(z) - (VNB-LAMBDA x. c)(z)' of `z |-> phi(z) - (VNB-LAMBDA x. 0)(z)';
;;;   (3) `antiderivative-transfer-ptwise-eq' moves BOTH slots at once -- onto
;;;       `z |-> f(z) - c' and onto phi -- which is exactly the two-slot case
;;;       that transfer's header says it exists for.
;;;
;;; Both `modulo 0'.
;;;
;;; ONE MECHANICAL POINT.  `mac-h' on the IS-ANTIDERIVATIVE hypothesis would
;;; DELETE it, and step (2) needs it as a whole to detach `antiderivative-sub';
;;; the endpoint facts come from the projection `antiderivative-endpoints'
;;; instead, which is what the projections in antiderivative.scm are for.
;;;
;;; Loads after antiderivative-transfer (antiderivative-sub,
;;; antiderivative-transfer-ptwise-eq), witness-family-choice
;;; (antiderivable-family-choice), continuity-basics (const-lam-in-fun,
;;; const-continuous-at), differentiation (deriv-const), ccint-basics
;;; (ccint-membership), binary-minus-laws (rr-sub-in-rr), fun-apply-type-proof
;;; and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `an-' prefix) --------------------

(define (an-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1))) #t))))

(define (an-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (an-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; beta to exhaustion, guarded on PROGRESS -- never on a call count.
(define (an-beta!)
  (let loop ((n 0) (g (dk-goal)))
    (if (> n 6) #t
        (begin (lam-b)
               (let ((g2 (dk-goal)))
                 (if (equal? g g2) #t (loop (+ n 1) g2)))))))

(define (an-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "an-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (an-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

;;; =====================================================================
;;; 1.  THE SHIFT.
;;; =====================================================================

(define an-cl '(VNB-LAMBDA x_ RR c))              ; the constant map
(define an-zl '(VNB-LAMBDA x_ RR 0))              ; the zero map
(define an-sh '(VNB-LAMBDA x_ RR (- (f x_) c)))   ; f shifted down by c

(sp (make-wff
  (forall-guarded '(f phi a b c)
    (list '(IN f (FUN RR RR)) '(IN phi (FUN RR RR)) '(IN a RR) '(IN b RR) '(IN c RR)
          '(IS-ANTIDERIVATIVE f phi a b))
    (list 'IS-ANTIDERIVATIVE an-sh 'phi 'a 'b))))
(quietly (lambda () (an-peel!)))
(quietly (lambda ()
  (fact 'rr-zero-in)
  (fact 'const-lam-in-fun 'c)
  (fact 'const-lam-in-fun 0)
  (dk-split! (dk-deepest (lambda () (fact 'antiderivative-endpoints 'f 'phi 'a 'b))))))

;;; (1) the constant map is an antiderivative of the zero map on [a,b]
(have! (list 'IS-ANTIDERIVATIVE an-cl an-zl 'a 'b)
  (lambda ()
    (quietly (lambda ()
      (mac 'IS-ANTIDERIVATIVE)
      (an-and!
       (lambda ()
         (let ((g (dk-goal)))
           (cond
             ((memq (car g) '(IN <)) (ass))
             ((eq? (car (cadr (caddr g))) 'IN)              ; continuity clause
              (let ((v (cadr (car (dk-landed (lambda () (di)))))))
                (mac-h 'ccint-membership (list 'IN v (list 'CCINT 'a 'b)))
                (dk-split! (car (dk-asms)))
                (fact 'const-continuous-at 'c v)
                (ass)))
             (else                                          ; derivative clause
              (di)
              (dk-split! (dk-landed-1 (lambda () (di))))
              (let ((v (caddr (dk-goal))))
                (have! (list 'AND '(IN c RR) (list 'IN v 'RR)))
                (fact 'deriv-const 'c v)
                (lam-b)
                (ass)))))))))))

;;; (2) Prop 4.8 subtracts it, (3) the two-slot transfer lands on the term wanted.
(define AN-SUB (dk-deepest
                 (lambda () (fact 'antiderivative-sub 'f an-cl 'phi an-zl 'a 'b))))
(define AN-SUBF   (cadr AN-SUB))
(define AN-SUBPHI (caddr AN-SUB))

(quietly (lambda ()
  (have! (list 'IN an-sh '(FUN RR RR))
    (lambda ()
      (dk-lam-t!)
      (let ((v (cadr (car (dk-landed (lambda () (di)))))))
        (fact 'fun-apply-type-c 'f 'RR 'RR v)
        (fact 'rr-sub-in-rr (list 'f v) 'c)
        (ass))))
  (have! (forall-guarded 'x_ '(IN x_ RR)
           (list '= (list an-sh 'x_) (list AN-SUBF 'x_)))
    (lambda ()
      (let ((v (cadr (car (dk-landed (lambda () (di)))))))
        (fact 'fun-apply-type-c 'f 'RR 'RR v)
        (fact 'rr-sub-in-rr (list 'f v) 'c)
        (an-beta!)
        (rfl))))
  (have! (forall-guarded 'x_ '(IN x_ RR)
           (list '= (list 'phi 'x_) (list AN-SUBPHI 'x_)))
    (lambda ()
      (let ((v (cadr (car (dk-landed (lambda () (di)))))))
        (fact 'fun-apply-type-c 'phi 'RR 'RR v)
        (an-beta!)
        (crs))))
  (fact 'antiderivative-transfer-ptwise-eq an-sh 'phi AN-SUBF AN-SUBPHI 'a 'b)
  (ass)))
(qed 'antiderivative-shift-const)
(topic! 'antiderivative-shift-const 'analysis)
(alias! 'antiderivative-shift-const
        "an antiderivative shifted by a constant is an antiderivative")

;;; =====================================================================
;;; 2.  THE NORMALISED FAMILY.  Prop 4.16's hypothesis (2) made true by
;;; construction rather than assumed.
;;; =====================================================================

(sp (make-wff "forall([phifam in fun(nn, fun(rr,rr)), a in rr, b in rr],
   forall([k_ in nn], is-antiderivable(phifam(k_), a, b)) implies
   forsome([fam in fun(nn, fun(rr,rr))],
      forall([k_ in nn], is-antiderivative(fam(k_), phifam(k_), a, b)
                         and (fam(k_))(a) = 0)))"))
(quietly (lambda () (an-peel!)))
(quietly (lambda () (fact 'antiderivable-family-choice 'phifam 'a 'b)))
(define AN-SK (an-skolem! (an-find 'ex (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))))))
(quietly (lambda () (dk-split! (car AN-SK))))
(define AN-F (car (cadr AN-SK)))
(define AN-FAM (an-find 'fam (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                              (dk-contains? f 'IS-ANTIDERIVATIVE)))))
(define (an-inner k) (list 'VNB-LAMBDA 'x_ 'RR
                       (list '- (list (list AN-F k) 'x_) (list (list AN-F k) 'a))))
(define an-lam (list 'VNB-LAMBDA 'k_ 'NN (an-inner 'k_)))

(have! (forall-guarded 'k_ '(IN k_ NN)
         (conjuncts->and
           (list (list 'IN (an-inner 'k_) '(FUN RR RR))
                 (list 'IS-ANTIDERIVATIVE (an-inner 'k_) '(phifam k_) 'a 'b)
                 (list '= (list (an-inner 'k_) 'a) 0))))
  (lambda ()
    (quietly (lambda ()
      (di)
      (dk-deepest (lambda () (inst+ AN-FAM 'k_)))
      (fact 'antiderivative-map-in-fun (list AN-F 'k_) '(phifam k_) 'a 'b)
      (fact 'antiderivative-fn-in-fun (list AN-F 'k_) '(phifam k_) 'a 'b)
      (fact 'fun-apply-type-c (list AN-F 'k_) 'RR 'RR 'a)
      (fact 'antiderivative-shift-const (list AN-F 'k_) '(phifam k_) 'a 'b
            (list (list AN-F 'k_) 'a))
      (fact 'antiderivative-map-in-fun (an-inner 'k_) '(phifam k_) 'a 'b)
      (an-and! (lambda ()
        (let ((g (dk-goal)))
          (if (eq? (car g) '=) (begin (an-beta!) (crs)) (ass)))))))))
(define AN-PT (car (dk-asms)))

(quietly (lambda ()
  (ew an-lam)
  (an-and!
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
           (begin
             (dk-lam-t!)
             (let ((z (cadr (car (dk-landed (lambda () (di)))))))
               (dk-split! (dk-deepest (lambda () (inst+ AN-PT z))))
               (ass)))
           (let ((z (cadr (car (dk-landed (lambda () (di)))))))
             (lam-b)
             (dk-split! (dk-deepest (lambda () (inst+ AN-PT z))))
             (an-and! (lambda () (ass))))))))))
(qed 'antiderivable-family-normalized)
(topic! 'antiderivable-family-normalized 'analysis)
(alias! 'antiderivable-family-normalized
        "a sequence of antiderivable functions has antiderivatives vanishing at a")
