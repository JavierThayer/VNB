;;; regulated-has-primitive.scm -- EVERY REGULATED FUNCTION HAS A PRIMITIVE on [a, b]
;;; (batch 22, stage 2: the assembly).
;;;
;;; THE SOURCE: Dieudonne, Foundations of Modern Analysis, (8.7.2): "any regulated mapping of I
;;; into F has a primitive in I."  Its proof: "from (8.6.4) and (7.6.1) it follows that we need
;;; only prove the theorem for step-functions."  The three parts are proven elsewhere:
;;;
;;;   (7.6.1) necessity   regulated-on-is-step-limit   (theorem-library/regulated-step-approx.scm)
;;;   step functions      step-fn-has-primitive        (theorem-library/primitive-glue.scm)
;;;   (8.6.4) on [a, b]   primitive-uniform-limit      (theorem-library/primitive-uniform-limit.scm)
;;;
;;; and this file joins them:
;;;
;;;   primitive-shift-const                 a primitive minus a constant is a primitive of the
;;;                                         same integrand
;;;   primitive-family-normalised-choice    if each f_k has a primitive, a SEQUENCE g_k of
;;;                                         primitives with g_k(a) = 0 exists (global choice)
;;;   regulated-on-has-primitive            (8.7.2) on [a, b]
;;;
;;; THE ASSEMBLY.  (7.6.1) gives a family fam of total step functions converging uniformly on
;;; [a, b] to EXTEND-CONST(f, a, b); the integrands are f_k = RESTRICT(fam(k), [a, b]), so that
;;; each has a primitive by the step-function case; the primitives are CHOSEN, one per k, and
;;; normalised to vanish at a (22-B's theorem is stated for normalised primitives: the constants
;;; g_k(a) are chosen rather than assumed to converge); the uniform-convergence hypothesis of
;;; 22-B, spelled out pointwise on [a, b], is read off IS-UNIF-LIMIT-ON through restrict-apply
;;; and extend-const-fixes; 22-B then gives the primitive of f.
;;;
;;; The shift is proved by citation, not by re-proving continuity and derivatives: the constant
;;; map -c (affine, slope 0) is a primitive of the zero map (pw-affine-antiderivative), and
;;; pw-antiderivative-sum adds it.
;;;
;;; Helper prefix: rhp-.  Lambda binders rhpy_, rhpz_, rhpfj_, rhpgj_, rhph_ occur nowhere else.
;;; =====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (rhp-head g) (and (pair? g) (car g)))

;;; close a goal (== L R) or (= L R) by the ring identity L = R, proved by `crs'.
(define (rhp-crs-close!)
  (let* ((g (dk-goal))
         (l (cadr g)) (r (caddr g))
         (eqn (if (dk-contains? r l) (list '= r l) (list '= l r))))   ; rewrite AWAY the side containing the other
    (if (eq? (car g) '=)
        (crs)
        (begin
          (dk-have! eqn (lambda () (crs)))
          (subst eqn)
          (qrfl)))))

;;; prove (IN lam (FUN dom RR)) by lam-t; POINTWISE lands the typing of the body at z.
(define (rhp-lam-t-on! lam dom pointwise)
  (dk-have! (list 'IN lam (list 'FUN dom 'RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (rhp-head (dk-goal)) 'FORALL))
             (ass)
             (let ((z (dk-di-var!)))
               (pointwise z)
               (ass))))
       (dk-opened (lambda () (lam-t)))))))

;;; the bounds of a point of CCINT(lo, hi), landed; the membership kept.
(define (rhp-ccint-parts! z lo hi)
  (fact 'ccint-elt-in-rr lo hi z)
  (dk-have! (list '<= lo z)
    (lambda () (dk-split-all! (dk-landed* (lambda ()
                 (mac-h 'ccint-membership (list 'IN z (list 'CCINT lo hi))))))
               (ass)))
  (dk-have! (list '<= z hi)
    (lambda () (dk-split-all! (dk-landed* (lambda ()
                 (mac-h 'ccint-membership (list 'IN z (list 'CCINT lo hi))))))
               (ass))))

;;; lo in CCINT(lo, hi), from lo < hi and the typings (in context).
(define (rhp-left-end! lo hi)
  (dk-have! (list '<= lo lo) (lambda () (dk-ineq! (list 'IN lo 'RR))))
  (dk-have! (list '<= lo hi) (lambda () (dk-ineq! (list 'IN lo 'RR) (list 'IN hi 'RR) (list '< lo hi))))
  (dk-have! (list 'IN lo (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))))

;;; =====================================================================
;;; (1) A PRIMITIVE SHIFTED BY A CONSTANT.
;;; =====================================================================

(sp (make-wff "forall([rhpg_, rhpf_, a, b, rhpc_ in rr], is-primitive(rhpg_, rhpf_, a, b) implies
   is-primitive(vnb-lambda(rhpy_, ccint(a, b), rhpg_(rhpy_) - rhpc_), rhpf_, a, b))"))
(dk-peel!)
(define rhp1-pr (dk-pick (dk-head? 'IS-PRIMITIVE) "the primitive"))
(define rhp1-g (list-ref rhp1-pr 1))
(define rhp1-f (list-ref rhp1-pr 2))
(define rhp1-a (list-ref rhp1-pr 3))
(define rhp1-b (list-ref rhp1-pr 4))
(define rhp1-t (cadr (dk-goal)))                       ; the shifted function, as the goal has it
(define rhp1-c (caddr (cadddr rhp1-t)))
(define rhp1-cab (list 'CCINT rhp1-a rhp1-b))
(fact 'primitive-in-fun rhp1-g rhp1-f rhp1-a rhp1-b)
(fact 'primitive-integrand-in-fun rhp1-g rhp1-f rhp1-a rhp1-b)
(dk-split-all! (list (dk-fact! 'primitive-endpoints rhp1-g rhp1-f rhp1-a rhp1-b)))
(fact 'rr-is-set)
(fact 'ccint-subset-rr rhp1-a rhp1-b)
(fact 'subclass-of-set-is-set rhp1-cab 'RR)
(fact 'rr-zero-in)
(fact 'rr-sub-in-rr 0 rhp1-c)

(define rhp1-mc (list '- 0 rhp1-c))
(define rhp1-aff (list 'VNB-LAMBDA 'rhpz_ rhp1-cab (list '+ rhp1-mc '(* 0 rhpz_))))
(define rhp1-zero (list 'VNB-LAMBDA 'rhpz_ rhp1-cab 0))

(rhp-lam-t-on! rhp1-t rhp1-cab
  (lambda (z)
    (fact 'fun-apply-type-c rhp1-g rhp1-cab 'RR z)
    (fact 'rr-sub-in-rr (list rhp1-g z) rhp1-c)))
(rhp-lam-t-on! rhp1-aff rhp1-cab
  (lambda (z)
    (fact 'ccint-elt-in-rr rhp1-a rhp1-b z)
    (fact 'rr-mul-in-rr 0 z)
    (fact 'rr-add-in-rr rhp1-mc (list '* 0 z))))
(rhp-lam-t-on! rhp1-zero rhp1-cab (lambda (z) 'nothing))

;; the constant map -c is a primitive of the zero map
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rhp1-cab)
            (list '== (list rhp1-aff 'pay_) (list '+ rhp1-mc '(* 0 pay_)))))
  (lambda () (dk-di-var!) (dk-lam-b!) (qrfl)))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rhp1-cab)
            (list '== (list rhp1-zero 'pay_) 0)))
  (lambda () (dk-di-var!) (dk-lam-b!) (qrfl)))
(dk-apply! (dk-fact! 'pw-affine-antiderivative rhp1-a rhp1-b) rhp1-mc 0 rhp1-aff rhp1-zero)

;; g - c = g + (-c), f = f + 0, pointwise
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rhp1-cab)
            (list '== (list rhp1-t 'pay_) (list '+ (list rhp1-g 'pay_) (list rhp1-aff 'pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr rhp1-a rhp1-b z)
      (fact 'fun-apply-type-c rhp1-g rhp1-cab 'RR z)
      (dk-lam-b!)
      (rhp-crs-close!))))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rhp1-cab)
            (list '== (list rhp1-f 'pay_) (list '+ (list rhp1-f 'pay_) (list rhp1-zero 'pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'fun-apply-type-c rhp1-f rhp1-cab 'RR z)
      (dk-lam-b!)
      (rhp-crs-close!))))
(dk-split-all! (list (dk-apply! (dk-fact! 'pw-antiderivative-sum rhp1-a rhp1-b rhp1-g rhp1-aff rhp1-f rhp1-zero)
                                rhp1-t rhp1-f)))
(ass)
(qed 'primitive-shift-const)
(topic! 'primitive-shift-const 'analysis)
(alias! 'primitive-shift-const
        "a primitive minus a constant is a primitive of the same function")

;;; =====================================================================
;;; (2) ONE NORMALISED PRIMITIVE PER INDEX, AS A FAMILY ON NN.  The witness-family-choice.scm
;;; pattern: the SEP of the normalised primitives of ff(k), inhabited by the shift of the given
;;; primitive, and k |-> CHOICE of it.  The family ff is untyped (a consumer instantiates it at a
;;; VNB-LAMBDA).
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr, rhpff_], forall([rhpk_ in nn], forsome([rhpg_],
     is-primitive(rhpg_, rhpff_(rhpk_), a, b))) implies
   forsome([rhpgf_ in fun(nn, fun(ccint(a, b), rr))], forall([rhpk_ in nn],
     is-primitive(rhpgf_(rhpk_), rhpff_(rhpk_), a, b) and (rhpgf_(rhpk_))(a) = 0)))"))
(define rhp2-ls (dk-peel!))
(define rhp2-h (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm 'IS-PRIMITIVE)))
                        "the primitives, one per index"))
(define rhp2-ff (car (list-ref (caddr (caddr (caddr rhp2-h))) 2)))   ; the family, as the context has it
(define rhp2-cab '(CCINT a b))
(define (rhp2-s k)
  (list 'SEP 'rhph_ (list 'FUN rhp2-cab 'RR)
    (list 'AND (list 'IS-PRIMITIVE 'rhph_ (list rhp2-ff k) 'a 'b) '(= (rhph_ a) 0))))
(define (rhp2-c k) (list 'CHOICE (rhp2-s k)))
(define rhp2-pt-form
  (list 'FORALL 'rhpk_
    (list 'IMPLIES '(IN rhpk_ NN)
      (list 'AND (list 'IN (rhp2-c 'rhpk_) (list 'FUN rhp2-cab 'RR))
        (list 'AND (list 'IS-PRIMITIVE (rhp2-c 'rhpk_) (list rhp2-ff 'rhpk_) 'a 'b)
                   (list '= (list (rhp2-c 'rhpk_) 'a) 0))))))
(dk-have! rhp2-pt-form
  (lambda ()
    (let* ((k (dk-di-var!))
           (g0 (dk-skolem! (dk-apply! rhp2-h k)))
           (fk (list rhp2-ff k)))
      (dk-split-all! (list (dk-fact! 'primitive-endpoints g0 fk 'a 'b)))
      (fact 'primitive-in-fun g0 fk 'a 'b)
      (rhp-left-end! 'a 'b)
      (fact 'fun-apply-type-c g0 rhp2-cab 'RR 'a)
      (let* ((sh (dk-fact! 'primitive-shift-const g0 fk 'a 'b (list g0 'a)))
             (h (cadr sh)))
        (fact 'primitive-in-fun h fk 'a 'b)
        (dk-have! (list '= (list h 'a) 0)
          (lambda () (dk-lam-b!) (crs)))
        (dk-split-all!
          (choose! (rhp2-s k) h
                   (lambda () (in-sep! (lambda () (ass))
                                       (lambda () (dk-conj-close! (lambda () (ass))))))))
        (dk-conj-close! (lambda () (ass)))))))
(define rhp2-pt (dk-pick (lambda (fm) (alpha-equiv? fm rhp2-pt-form)) "the per-index facts"))

(define rhp2-fam (list 'VNB-LAMBDA 'rhpgj_ 'NN (rhp2-c 'rhpgj_)))
(ew rhp2-fam)
(dk-conj-close!
  (lambda ()
    (if (eq? (rhp-head (dk-goal)) 'IN)
        (begin
          (dk-lam-t!)
          (let ((k (dk-di-var!)))
            (dk-split-all! (list (dk-apply! rhp2-pt k)))
            (ass)))
        (let ((k (dk-di-var!)))
          (dk-lam-b!)
          (dk-split-all! (list (dk-apply! rhp2-pt k)))
          (dk-conj-close! (lambda () (ass)))))))
(qed 'primitive-family-normalised-choice)
(topic! 'primitive-family-normalised-choice 'analysis)
(alias! 'primitive-family-normalised-choice
        "a sequence of functions with primitives has a sequence of primitives vanishing at a")

;;; =====================================================================
;;; (3) DIEUDONNE (8.7.2) ON [a, b]: A REGULATED FUNCTION HAS A PRIMITIVE.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr, f], is-regulated-on(f, a, b) implies
   forsome([g], is-primitive(g, f, a, b)))"))
(dk-peel!)
(dk-have! '(AND (< a b) (IN f (FUN (CCINT a b) RR)))
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-regulated-on '(IS-REGULATED-ON f a b)))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all! (list '(AND (< a b) (IN f (FUN (CCINT a b) RR)))))
(define rhp3-cab '(CCINT a b))
(fact 'rr-lt-implies-le 'a 'b)
(fact 'ccint-subset-rr 'a 'b)
(define rhp3-e '(EXTEND-CONST f a b))
(dk-fact! 'extend-const-in-fun 'a 'b 'f)

;; (7.6.1): the step approximants
(define rhp3-fam (dk-skolem! (dk-fact! 'regulated-on-is-step-limit 'a 'b 'f)))
(dk-split-all!)
(define rhp3-step (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm 'IS-STEP-FN)))
                           "the approximants are step functions"))
(define rhp3-ul-pred (dk-pick (dk-head? 'IS-UNIF-LIMIT-ON) "the uniform limit"))

;; the integrands f_k = RESTRICT(fam(k), [a, b])
(define rhp3-ff (list 'VNB-LAMBDA 'rhpfj_ 'NN (list 'RESTRICT (list rhp3-fam 'rhpfj_) rhp3-cab)))
(dk-have! (list 'IN rhp3-ff (list 'FUN 'NN (list 'FUN rhp3-cab 'RR)))
  (lambda ()
    (dk-lam-t!)
    (let ((k (dk-di-var!)))
      (fact 'fun-apply-type-c rhp3-fam 'NN '(FUN RR RR) k)
      (fact 'restrict-in-fun (list rhp3-fam k) 'RR 'RR rhp3-cab)
      (ass))))

;; each f_k has a primitive (the step-function case), hence a normalised family of them
(define rhp3-nc (dk-fact! 'primitive-family-normalised-choice 'a 'b rhp3-ff))
(define rhp3-gex
  (dk-apply!
    (detach-with! rhp3-nc
      (lambda ()
        (let ((k (dk-di-var!)))
          (dk-lam-b!)
          (dk-apply! rhp3-step k)
          (fact 'step-fn-has-primitive 'a 'b (list rhp3-fam k))
          (ass))))))
(define rhp3-gfam (dk-skolem! rhp3-gex))
(define rhp3-gpt (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm rhp3-gfam)))
                          "the normalised primitives"))

;; the uniform convergence, read off IS-UNIF-LIMIT-ON on [a, b]
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-unif-limit-on rhp3-ul-pred))))
(define rhp3-ul (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm 'POS-RR)
                                           (dk-contains? fm rhp3-fam)))
                         "the uniform estimate"))

(define (rhp3-uniform!)
  (let* ((ls (dk-peel!))
         (e (cadr (find-first (dk-head? 'POS-RR) ls)))
         (n (dk-skolem! (dk-apply! rhp3-ul e)))
         (un (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm n)
                                        (dk-contains? fm rhp3-fam)))
                      "the uniform clause at e")))
    (ew n)
    (dk-conj-close!
      (lambda ()
        (if (eq? (rhp-head (dk-goal)) 'IN)
            (ass)
            (let* ((ls2 (dk-peel!))
                   (k (cadr (find-first (lambda (fm) (and ((dk-head? 'IN) fm) (eq? (caddr fm) 'NN))) ls2)))
                   (x (cadr (find-first (lambda (fm) (and ((dk-head? 'IN) fm) (dk-contains? fm 'CCINT))) ls2)))
                   (fk (list rhp3-fam k))
                   (fkx (list fk x))
                   (fx (list 'f x))
                   (ex (list rhp3-e x)))
              (dk-apply! (detach-with! (inst*! un k) (lambda () (dk-conj-close! (lambda () (ass))))) x)
              (rhp-ccint-parts! x 'a 'b)
              (fact 'fun-apply-type-c rhp3-fam 'NN '(FUN RR RR) k)
              (fact 'fun-apply-type-c fk 'RR 'RR x)
              (fact 'fun-apply-type-c 'f rhp3-cab 'RR x)
              (fact 'restrict-apply fk rhp3-cab x)
              (dk-apply! (dk-fact! 'extend-const-fixes 'a 'b x) 'f)
              (dk-lam-b!)
              (subst (list '= (list (list 'RESTRICT fk rhp3-cab) x) fkx))
              (subst (dk-fact! 'rr-abs-sub-sym fkx fx))
              (subst (list '= fx ex))
              (ass)))))))

;; (8.6.4): the limit of the normalised primitives is a primitive of f
(define rhp3-ch (inst*! (dk-fact! 'primitive-uniform-limit 'a 'b) rhp3-gfam rhp3-ff 'f))
(define rhp3-ch2
  (detach-with! rhp3-ch
    (lambda ()
      (let ((k (dk-di-var!)))
        (dk-split-all! (list (dk-apply! rhp3-gpt k)))
        (ass)))))
(define rhp3-ch3 (detach-with! rhp3-ch2 rhp3-uniform!))
(define rhp3-res
  (detach-with! rhp3-ch3
    (lambda ()
      (let ((k (dk-di-var!)))
        (dk-split-all! (list (dk-apply! rhp3-gpt k)))
        (ass)))))
(define rhp3-g (dk-skolem! rhp3-res))
(ew rhp3-g)
(ass)
(qed 'regulated-on-has-primitive)
(topic! 'regulated-on-has-primitive 'analysis)
(alias! 'regulated-on-has-primitive
        "Dieudonne (8.7.2)"
        "every regulated function on [a, b] has a primitive on [a, b]")
