;;; inverse-function.scm -- THE INVERSE FUNCTION THEOREM ON THE LINE,
;;; Caratheodory form, PROVEN:
;;;
;;;   IS-DIFF-AT(f, a, L),  L /= 0,  g a two-sided inverse of f,
;;;   g continuous at f(a)          =>   IS-DIFF-AT(g, f(a), recip(L))
;;;
;;; The user's calculus notes (docs/calculus.pdf, Chapter 2) have NO inverse
;;; function section -- the chapter runs Definitions / o-O / Chain Rule /
;;; Extrema / MVT / Taylor / Polynomials / Multivariable -- so this is stated at
;;; the notes' level of generality for differentiation, which is the real line.
;;; The R^n contraction-mapping version is deliberately out of scope.
;;;
;;; WHICH THEOREM THIS IS, AND WHICH IT IS NOT.  It is the GLOBAL statement, and
;;; that is forced, not chosen.  `IS-DIFF-AT(f,a,L)' (differentiation.scm:35)
;;; opens with `(IN f (FUN RR RR))': in this vocabulary a differentiable map is
;;; total on RR, and "f restricted to a neighbourhood of a" is not a term the
;;; tree can form -- the same wall the neighbourhood form of the CHAIN RULE hit
;;; (theorem-library/chain-rule.scm), and for the same reason: there is no
;;; metric SUBSPACE structure.  So:
;;;
;;;   PROVED    f, g : RR -> RR with g(f(x)) = x and f(g(y)) = y for EVERY real
;;;             x, y -- i.e. f a bijection of RR with inverse g -- f
;;;             differentiable at a with f'(a) /= 0, g continuous at f(a).
;;;             Then g is differentiable at f(a) with derivative 1/f'(a).
;;;
;;;   NOT PROVED   the local statement: f differentiable on a neighbourhood of
;;;                a with f'(a) /= 0 implies f is invertible NEAR a and the
;;;                local inverse is differentiable at f(a).  Both halves of that
;;;                are out of reach -- the existence half wants monotonicity on
;;;                an interval (see the note at the end of this file), and even
;;;                the derivative half cannot be stated without a restriction.
;;;
;;; Continuity of g is a HYPOTHESIS and not a conclusion, which is the honest
;;; reading: with only the Caratheodory factorization in hand there is nothing
;;; to derive it from.  (Classically it comes from monotonicity, which is the
;;; half of the subject the tree has no vocabulary for.)
;;;
;;; WHY IT IS CHEAP.  Caratheodory again.  With f(x) - f(a) = phi(x)(x-a),
;;; phi continuous at a and phi(a) = L, put y = f(x), so x = g(y):
;;;
;;;     y - f(a)  =  phi(g(y)) * (g(y) - g(f(a)))
;;;
;;; and dividing by phi(g(y)) -- which is legitimate because phi NEVER vanishes
;;; -- gives the Caratheodory factorization of g at f(a) with factor
;;; psi = recip o phi o g.  So the witness is
;;;
;;;     psi  =  (VNB-LAMBDA y RR (recip ((COMPOSE phi g) y)))
;;;
;;; and psi(f(a)) = recip(phi(a)) = recip(L).  The analytic content is that psi
;;; is continuous at f(a), and that is `compose-continuous-at'
;;; (continuity-compose.scm) followed by `recip-continuous-at'
;;; (continuity-recip.scm), both proven; no eps and no delta appear in this
;;; file.
;;;
;;; PHI NEVER VANISHES, and that is where the inverse hypothesis is really
;;; used.  If phi(x) = 0 then f(x) - f(a) = 0*(x-a) = 0, so f(x) = f(a); apply
;;; g and x = g(f(x)) = g(f(a)) = a; but then phi(x) = phi(a) = L /= 0.  No case
;;; split is needed -- x = a is DERIVED and then contradicted, rather than being
;;; one branch of an excluded middle.
;;;
;;; WHAT IT COSTS: `modulo {compose-type, compose-apply}' [trust: proof] --
;;; inherited entire from compose-continuous-at, and coming from the two COMPOSE
;;; laws of structure-library/compose.scm, both `warrant! 'proof' supports whose
;;; warrant text is a one-line derivation that has never been run.  Everything
;;; else is zero.
;;;
;;; DRIVER NOTES.
;;;
;;; * `mac-h' is destructive, so the two inverse universals and the continuity
;;;   of g are read off the context BEFORE `IS-DIFF-AT(f,a,L)' is unfolded.
;;; * The two inverse universals have the SAME shape -- FORALL/IMPLIES/= -- and
;;;   are told apart on the HEAD of their consequent's left-hand side: g(f(v))
;;;   for one, f(g(v)) for the other.
;;; * The Caratheodory factor phi is the subject of the continuity assumption
;;;   whose POINT is a; g's own continuity is at f(a), so the point alone
;;;   discriminates.
;;; * The witness psi is not rebuilt by hand: `recip-continuous-at' concludes
;;;   about the literal term (VNB-LAMBDA x RR (recip (H x))), and that term,
;;;   read off the landing, IS the existential witness.
;;;
;;; WHAT IS STILL MISSING -- the EXISTENCE half.  "f continuous and strictly
;;; increasing on [a,b] has a continuous strictly increasing inverse on
;;; [f(a),f(b)]" is NOT in this file and is not proved anywhere in the tree.
;;; The obstacle is vocabulary, not analysis: there is no monotonicity predicate
;;; for real functions at all (the only IS-STRICTLY-* in the tree is
;;; IS-STRICTLY-BELOW, a poset relation in zorn-route-two.scm), and
;;; deriv-monotone-proof.scm writes "strictly increasing on [a,b]" out longhand
;;; each time.  See the head comment of theorem-library/monotone-inverse.scm.
;;;
;;; Loads after chain-rule (which needs the same COMPOSE laws) and
;;; continuity-recip; needs differentiation (IS-DIFF-AT), continuity-compose
;;; (compose-continuous-at), continuity-recip (recip-lam-in-fun,
;;; recip-continuous-at), compose (compose-type, compose-apply),
;;; fun-apply-type-proof, rr-order-basics (rr-sub-in-rr), driver-kit.

;;; ---- file-local driver helpers (the `ifp-' prefix) --------------------

(define (ifp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))
(define (ifp-split!)
  (let loop ((b 40))
    (when (> b 0)
      (let ((t (let scan ((as (dk-asms)))
                 (cond ((null? as) #f)
                       ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                       (else (scan (cdr as)))))))
        (when t (ai t) (loop (- b 1)))))))
(define (ifp-find what p)
  (let lp ((l (dk-asms)))
    (cond ((null? l) (error "ifp-find" what)) ((p (car l)) (car l)) (else (lp (cdr l))))))
(define (ifp-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ifp-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (ifp-has-redex? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (ifp-has-redex? (car g)) (ifp-has-redex? (cdr g))))
        (else #f)))
(define (ifp-beta!)
  (let loop ((fuel 8))
    (if (and (> fuel 0) (ifp-has-redex? (dk-goal)))
        (let ((b (dk-goal))) (lam-b) (if (equal? (dk-goal) b) #t (loop (- fuel 1))))
        #t)))


;;; =====================================================================
;;; (1) Solving a product equation for its second factor.
;;;
;;;     c /= 0,  u = c*v   ==>   v = recip(c) * u
;;;
;;; The one algebraic step of the theorem below, isolated because `crs' does not
;;; read hypotheses: the reassociation (recip c)*(c*v) = (c*recip c)*v is a ring
;;; identity in the opaque generator recip(c), and it is the `subst' of
;;; rr-recip-inverse afterwards that collapses it.
;;; =====================================================================

(sp (make-wff (forall-guarded '(c u v) (list '(IN c RR) '(IN u RR) '(IN v RR))
   '(IMPLIES (NOT (= c 0)) (IMPLIES (= u (* c v)) (= v (* (recip c) u)))))))
(ifp-peel!)
(have! '(AND (IN c RR) (NOT (= c 0))))
(fact 'rr-recip-closed 'c)
(fact 'rr-recip-inverse 'c)
(subst '(= u (* c v)))
(have! '(= (* (recip c) (* c v)) (* (* c (recip c)) v)) (lambda () (crs)))
(subst '(= (* (recip c) (* c v)) (* (* c (recip c)) v)))
(subst '(= (* c (recip c)) 1))
(crs)
(qed 'rr-recip-solve)
(topic! 'rr-recip-solve 'algebra)
(alias! 'rr-recip-solve "solving u = c*v for v")

;;; =====================================================================
;;; (2) deriv-inverse.
;;; =====================================================================

(sp (make-wff
  (forall-guarded '(f g a L)
    (list '(IS-DIFF-AT f a L)
          '(NOT (= L 0))
          '(IN g (FUN RR RR))
          '(FORALL x (IMPLIES (IN x RR) (= (g (f x)) x)))
          '(FORALL y (IMPLIES (IN y RR) (= (f (g y)) y)))
          '(IS-CONTINUOUS-AT RR-MS RR-MS g (f a)))
    '(IS-DIFF-AT g (f a) (recip L)))))
(dk-peel-to! 'IS-DIFF-AT)

(define iv-f #f) (define iv-g #f) (define iv-a #f) (define iv-l #f)
(define iv-phi #f) (define iv-h #f) (define iv-psi #f)
(define iv-aph #f) (define iv-idphi #f) (define iv-gf #f) (define iv-fg #f)
(define iv-nzphi #f)

(let* ((g0 (dk-goal)) (fa (list-ref g0 2)))
  (set! iv-g (list-ref g0 1))
  (set! iv-f (car fa))
  (set! iv-a (cadr fa))
  (set! iv-l (cadr (list-ref g0 3))))

;; the two inverse universals, discriminated on the HEAD of their consequent's LHS
(define (iv-univ head)
  (ifp-find head
    (lambda (u) (and (pair? u) (eq? (car u) 'FORALL)
                     (pair? (caddr u)) (eq? (car (caddr u)) 'IMPLIES)
                     (let ((c (caddr (caddr u))))
                       (and (pair? c) (eq? (car c) '=) (pair? (cadr c))
                            (eq? (car (cadr c)) head)))))))
(set! iv-gf (iv-univ iv-g))
(set! iv-fg (iv-univ iv-f))

(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT iv-f iv-a iv-l))
(ifp-split!)
(set! iv-phi (list-ref (ifp-find 'phi-cont
   (lambda (u) (and (pair? u) (eq? (car u) 'IS-CONTINUOUS-AT) (equal? (list-ref u 4) iv-a)))) 3))
(set! iv-idphi (ifp-find 'phi-id
   (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (dk-contains? u iv-phi)
                    (pair? (caddr u)) (eq? (car (caddr u)) 'IMPLIES)
                    (let ((c (caddr (caddr u))))
                      (and (pair? c) (eq? (car c) '=) (pair? (caddr c))
                           (eq? (car (caddr c)) '*)))))))

(fact 'fun-apply-type-c iv-f 'RR 'RR iv-a)          ; (IN (f a) RR)
(inst+ iv-gf iv-a)                                  ; (= (g (f a)) a)
(define iv-fa (list iv-f iv-a))

;;; phi is nowhere zero
(set! iv-nzphi (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
                    (list 'NOT (list '= (list iv-phi 'x) 0)))))
(have! iv-nzphi
  (lambda ()
    (let* ((landed (dk-landed (lambda () (di))))
           (x (cadr (car landed))))
      (di)                                          ; assume (= (phi x) 0), goal FALSITY
      (inst+ iv-idphi x)
      (fact 'fun-apply-type-c iv-f 'RR 'RR x)
      (fact 'fun-apply-type-c iv-phi 'RR 'RR x)
      (fact 'rr-sub-in-rr x iv-a)
      (fact 'rr-sub-in-rr (list iv-f x) iv-fa)
      (have! (list '= (list '- (list iv-f x) iv-fa) 0)
        (lambda ()
          (subst (list '= (list '- (list iv-f x) iv-fa)
                          (list '* (list iv-phi x) (list '- x iv-a))))
          (subst (list '= (list iv-phi x) 0))
          (crs)))
      (have! (list '= (list iv-f x) iv-fa)
        (lambda ()
          (have! (list '= (list iv-f x)
                          (list '+ (list '- (list iv-f x) iv-fa) iv-fa))
                 (lambda () (crs)))
          (subst (list '= (list iv-f x)
                          (list '+ (list '- (list iv-f x) iv-fa) iv-fa)))
          (subst (list '= (list '- (list iv-f x) iv-fa) 0))
          (crs)))
      (inst+ iv-gf x)                               ; (= (g (f x)) x)
      (have! (list '= x iv-a)
        (lambda ()
          (fact 'eq-sym (list iv-g (list iv-f x)) x)
          (subst (list '= x (list iv-g (list iv-f x))))
          (subst (list '= (list iv-f x) iv-fa))
          (ass)))
      (have! (list '= iv-l 0)
        (lambda ()
          (fact 'eq-sym (list iv-phi iv-a) iv-l)
          (subst (list '= iv-l (list iv-phi iv-a)))
          (fact 'eq-sym x iv-a)
          (subst (list '= iv-a x))
          (ass)))
      (ai (list 'NOT (list '= iv-l 0))))))

;;; H = phi o g
(set! iv-h (list 'COMPOSE iv-phi iv-g))
;; compose-type is GUARDED on (IN A SET) since 2026-08-23; A = RR here.
(fact 'rr-is-set)
(have! (list 'AND (list 'IN iv-g '(FUN RR RR)) (list 'IN iv-phi '(FUN RR RR))))
(fact 'compose-type 'RR 'RR 'RR iv-phi iv-g)
(set! iv-aph (dk-fact! 'compose-apply 'RR 'RR 'RR iv-phi iv-g))

(have! (list 'FORALL 'x (list 'IMPLIES '(IN x RR) (list 'NOT (list '= (list iv-h 'x) 0))))
  (lambda ()
    (let* ((landed (dk-landed (lambda () (di))))
           (y (cadr (car landed))))
      (inst+ iv-aph y)
      (subst (list '= (list iv-h y) (list iv-phi (list iv-g y))))
      (fact 'fun-apply-type-c iv-g 'RR 'RR y)
      (inst+ iv-nzphi (list iv-g y))
      (ass))))

(have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS iv-phi (list iv-g iv-fa))
  (lambda () (subst (list '= (list iv-g iv-fa) iv-a)) (ass)))
(fact 'compose-continuous-at iv-phi iv-g iv-fa)
(fact 'recip-lam-in-fun iv-h)
(set! iv-psi (list-ref (dk-fact! 'recip-continuous-at iv-h iv-fa) 3))
(have! (list 'AND (list 'IN iv-l 'RR) (list 'NOT (list '= iv-l 0))))
(fact 'rr-recip-closed iv-l)

(mac 'IS-DIFF-AT)
(ifp-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORSOME)
       (begin
         (ew iv-psi)
         (ifp-and!
          (lambda ()
            (let ((h (dk-goal)))
              (cond
               ((eq? (car h) '=)
                (ifp-beta!)
                (inst+ iv-aph iv-fa)
                (subst (list '= (list iv-h iv-fa) (list iv-phi (list iv-g iv-fa))))
                (subst (list '= (list iv-g iv-fa) iv-a))
                (subst (list '= (list iv-phi iv-a) iv-l))
                (rfl))
               ((eq? (car h) 'FORALL)
                (let* ((landed (dk-landed (lambda () (di))))
                       (y (cadr (car landed)))
                       (gy (list iv-g y))
                       (c (list iv-phi gy))
                       (u (list '- y iv-fa))
                       (v (list '- gy iv-a)))
                  (ifp-beta!)
                  (inst+ iv-aph y)
                  (subst (list '= (list iv-h y) c))
                  (subst (list '= (list iv-g iv-fa) iv-a))
                  (fact 'fun-apply-type-c iv-g 'RR 'RR y)
                  (fact 'fun-apply-type-c iv-phi 'RR 'RR gy)
                  (fact 'rr-sub-in-rr y iv-fa)
                  (fact 'rr-sub-in-rr gy iv-a)
                  (inst+ iv-nzphi gy)
                  (have! (list '= u (list '* c v))
                    (lambda ()
                      (inst+ iv-idphi gy)
                      (inst+ iv-fg y)
                      (have! (list '= u (list '- (list iv-f gy) iv-fa))
                        (lambda () (subst (list '= (list iv-f gy) y)) (rfl)))
                      (subst (list '= u (list '- (list iv-f gy) iv-fa)))
                      (ass)))
                  (fact 'rr-recip-solve c u v)
                  (ass)))
               (else (ass)))))))
       (ass))))
(qed 'deriv-inverse)
(topic! 'deriv-inverse 'analysis)
(alias! 'deriv-inverse "the derivative of an inverse function"
        "inverse function theorem (derivative form)")
