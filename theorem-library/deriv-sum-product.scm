;;; deriv-sum-product.scm -- calculus.pdf Prop 2.5 (the SUM rule) and Prop 2.6
;;; (the PRODUCT rule), PROVEN, both `modulo 0'.
;;;
;;;   IS-DIFF-AT(f,a,L), IS-DIFF-AT(g,a,M)
;;;      =>  IS-DIFF-AT(lambda x in RR. f(x)+g(x),  a,  L+M)
;;;      =>  IS-DIFF-AT(lambda x in RR. f(x)*g(x),  a,  L*g(a)+f(a)*M)
;;;
;;; Both stood in theorem-library/differentiation.scm as `support' +
;;; `warrant! 'reference' pointing at the notes, and both warrant TEXTS were the
;;; derivation written in prose and then not run -- the same species as
;;; `compose-apply', `fun-apply-type-c' and `integral-domain-nontrivial'.  The
;;; statements are reproduced VERBATIM from there, so any citation reads exactly
;;; as before.  This time the prose was RIGHT; what it left out is below.
;;;
;;; WHY THERE IS NO EPSILON HERE.  IS-DIFF-AT is Caratheodory
;;; (differentiation.scm:35): f is differentiable at a with derivative L iff
;;; there is a phi, continuous at a, with phi(a) = L and
;;; f(x) - f(a) = phi(x)*(x - a) for every real x.  So each rule is an ALGEBRAIC
;;; identity in the factors plus one citation from the continuity algebra:
;;;
;;;   sum      phi = phi_f + phi_g
;;;            (f+g)(x) - (f+g)(a) = (phi_f(x) + phi_g(x))(x - a)
;;;   product  phi = phi_f . g + f(a) . phi_g          [add and subtract f(a)g(x)]
;;;            (fg)(x) - (fg)(a) = (phi_f(x)g(x) + f(a)phi_g(x))(x - a)
;;;
;;; and both identities are closed by `crs' once the two factorization
;;; hypotheses have been substituted in.
;;;
;;; THE ONE STEP THE WARRANTS DO NOT MENTION, and it is what makes the product
;;; rule cost more than the sum rule: the product WITNESS is continuous at a
;;; only because g is continuous at a, which is Prop 2.4
;;; (`diff-implies-continuous'), not part of the hypothesis as stated.  And
;;; `mac-h' REPLACES the assumption it unfolds, so IS-DIFF-AT(g,a,M) is GONE by
;;; the time the witness is assembled.  The citation therefore has to be made
;;; BEFORE the unfold -- one line, in the wrong place by one step and the whole
;;; proof fails several steps later with a `fact' that silently lands an
;;; implication instead of its consequent.
;;;
;;; THE WITNESS IS BUILT FROM BLOCK LAMBDAS, not written out.  `sum-lam-in-fun',
;;; `prod-lam-in-fun', `sum-continuous-at', `product-continuous-at' and
;;; `const-continuous-at' all conclude about the LITERAL term
;;; (VNB-LAMBDA x RR (+ (g x) (h x))) etc., with g and h instantiated at whole
;;; function terms -- they cannot be backchained, because (g x) is
;;; higher-order.  So the product witness is assembled as
;;;
;;;   P1 = lambda x in RR. phi_f(x) * g(x)          prod-lam-in-fun(phi_f, g)
;;;   K  = lambda x in RR. f(a)                     const-lam-in-fun(f(a))
;;;   P2 = lambda x in RR. K(x) * phi_g(x)          prod-lam-in-fun(K, phi_g)
;;;   W  = lambda x in RR. P1(x) + P2(x)            sum-lam-in-fun(P1, P2)
;;;
;;; -- the same layered-lambda idiom `diff-implies-continuous' uses one file
;;; up.  The redexes are left UNREDUCED in the terms handed to `ew' and to the
;;; citations, and reduced by `lam-b' only on the goals that need it; that is
;;; what lets the citations match by `ass' rather than by luck.
;;;
;;; Needs differentiation (IS-DIFF-AT, diff-implies-continuous), continuity-sum
;;; (sum-lam-in-fun, sum-continuous-at), continuity-product (prod-lam-in-fun,
;;; product-continuous-at), continuity-basics (const-lam-in-fun,
;;; const-continuous-at), fun-apply-type-proof (fun-apply-type-c) and
;;; driver-kit (have!, dk-*).

;;; ---- file-local driver helpers (the `dsp-' prefix; never named like a
;;; tactic, and every assumption selected by CONTENT, not by position) ------

;; split every conjunctive / existential assumption, skolemizing the FORSOMEs
(define (dsp-split!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 30)) (begin (ai tgt) (loop (+ n 1)))))))

;; the assumption (= (PHI pt) VAL) names the skolem Caratheodory factor PHI.
;; The two factors are told apart by their VALUE (L vs M), never by context
;; order, which is not the peel order.
(define (dsp-phi-for pt val)
  (let ((h (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                      (equal? (caddr a) val)
                                      (pair? (cadr a)) (= (length (cadr a)) 2)
                                      (equal? (cadr (cadr a)) pt)))
                     (dk-asms))))
    (if h (car (cadr h)) (error "dsp-phi-for: no factor assumption for" val))))

;; the Caratheodory factorization universal mentioning PHI
(define (dsp-diffid phi)
  (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a phi)))
                (dk-asms))
      (error "dsp-diffid: no factorization assumption for" phi)))

;; lam-b the goal to a fixpoint (the block lambdas nest, so one call is not
;; enough; every argument in sight is typed in RR before this runs)
(define (dsp-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;; (IN (+ u v) RR) / (IN (* u v) RR) -- rr-add-closed and rr-mul-closed have AND
;; antecedents, which `fact' will not split, so the conjunction goes in first.
(define (dsp-add! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-add-closed u v))
(define (dsp-mul! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;;; =====================================================================
;;; Prop 2.5 -- the SUM rule.  Statement VERBATIM from differentiation.scm.
;;; =====================================================================

(sp (make-wff
 '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
    (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
             (IS-DIFF-AT (VNB-LAMBDA x RR (+ (f x) (g x))) a (+ L M))))))))))
(dk-peel-to! 'IS-DIFF-AT)

;;; Everything read off the GOAL, which names each eigenvariable in its role.
(define ds-lam (cadr (dk-goal)))                  ; lambda x in RR. f(x)+g(x)
(define ds-pt  (caddr (dk-goal)))                 ; a
(define ds-bod (cadddr ds-lam))                   ; (+ (f x) (g x))  -- caddr is RR
(define ds-f   (car (cadr ds-bod)))               ; f
(define ds-g   (car (caddr ds-bod)))              ; g
(define ds-l   (cadr (cadddr (dk-goal))))         ; L     (from (+ L M))
(define ds-m   (caddr (cadddr (dk-goal))))        ; M

(dk-ai-head! 'AND)
(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT ds-f ds-pt ds-l))
(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT ds-g ds-pt ds-m))
(dsp-split!)

(define ds-pf (dsp-phi-for ds-pt ds-l))           ; phi_f
(define ds-pg (dsp-phi-for ds-pt ds-m))           ; phi_g
(define ds-hf (dsp-diffid ds-pf))                 ; f's factorization universal
(define ds-hg (dsp-diffid ds-pg))
(define ds-w (list 'VNB-LAMBDA 'x 'RR (list '+ (list ds-pf 'x) (list ds-pg 'x))))

;;; Landed BEFORE the goal is split, so every branch has them: (IN (L+M) RR) is
;;; also the definedness witness `rfl' wants three leaves down.
(dsp-add! ds-l ds-m)
(fact 'sum-lam-in-fun ds-f ds-g)                  ; the goal lambda is a function
(fact 'sum-lam-in-fun ds-pf ds-pg)                ; so is the witness
(fact 'sum-continuous-at ds-pf ds-pg ds-pt)       ; and it is continuous at a

(mac 'IS-DIFF-AT)
(di) (ass)                                        ; lambda in FUN(RR,RR)
(di) (ass)                                        ; a in RR
(di) (ass)                                        ; L+M in RR
(ew ds-w)                                         ; phi := phi_f + phi_g
(di) (ass)                                        ; witness typing
(di) (ass)                                        ; witness continuity
(di) (dsp-beta!)                                  ; W(a) = phi_f(a) + phi_g(a)
(subst (list '= (list ds-pf ds-pt) ds-l))
(subst (list '= (list ds-pg ds-pt) ds-m))
(rfl)
;;; the factorization.  (f+g)(x)-(f+g)(a) = (phi_f(x)+phi_g(x))(x-a): distribute
;;; the RIGHT side into two products, replace each by the factorization it comes
;;; from, and what is left is a ring identity in f(x), f(a), g(x), g(a).
(let ((z (cadr (car (dk-landed* (lambda () (di)))))))
  (dsp-beta!)
  (inst+ ds-hf z)                                 ; f(x)-f(a) = phi_f(x)(x-a)
  (inst+ ds-hg z)                                 ; g(x)-g(a) = phi_g(x)(x-a)
  (fact 'fun-apply-type-c ds-pf 'RR 'RR z)
  (fact 'fun-apply-type-c ds-pg 'RR 'RR z)
  (fact 'fun-apply-type-c ds-f 'RR 'RR z)
  (fact 'fun-apply-type-c ds-g 'RR 'RR z)
  (fact 'fun-apply-type-c ds-f 'RR 'RR ds-pt)
  (fact 'fun-apply-type-c ds-g 'RR 'RR ds-pt)
  (fact 'rr-sub-in-rr z ds-pt)
  (let* ((d  (list '- z ds-pt))
         (p  (list ds-pf z))
         (q  (list ds-pg z))
         (fd (list '- (list ds-f z) (list ds-f ds-pt)))
         (gd (list '- (list ds-g z) (list ds-g ds-pt)))
         (dist (list '= (list '* (list '+ p q) d)
                        (list '+ (list '* p d) (list '* q d)))))
    (have! dist (lambda () (crs)))
    (subst dist)
    (fact 'eq-sym fd (list '* p d))               ; phi_f(x)(x-a) = f(x)-f(a)
    (subst (list '= (list '* p d) fd))
    (fact 'eq-sym gd (list '* q d))
    (subst (list '= (list '* q d) gd))
    (crs)))
(qed 'deriv-sum)
(topic! 'deriv-sum 'analysis)
(alias! 'deriv-sum "the derivative of a sum is the sum of the derivatives")

;;; =====================================================================
;;; Prop 2.6 -- the PRODUCT rule.  Statement VERBATIM from differentiation.scm.
;;; =====================================================================

(sp (make-wff
 '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
    (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
             (IS-DIFF-AT (VNB-LAMBDA x RR (* (f x) (g x))) a
                         (+ (* L (g a)) (* (f a) M)))))))))))
(dk-peel-to! 'IS-DIFF-AT)

(define dp-lam (cadr (dk-goal)))                  ; lambda x in RR. f(x)*g(x)
(define dp-pt  (caddr (dk-goal)))                 ; a
(define dp-bod (cadddr dp-lam))                   ; (* (f x) (g x))  -- caddr is RR
(define dp-f   (car (cadr dp-bod)))               ; f
(define dp-g   (car (caddr dp-bod)))              ; g
(define dp-l   (cadr (cadr (cadddr (dk-goal)))))  ; L  (from (+ (* L (g a)) ...))
(define dp-m   (caddr (caddr (cadddr (dk-goal)))))    ; M

(dk-ai-head! 'AND)
;;; BEFORE the unfold: `mac-h' replaces the hypothesis, and the product witness
;;; needs g CONTINUOUS at a, which only IS-DIFF-AT(g,a,M) can supply (Prop 2.4).
(fact 'diff-implies-continuous dp-g dp-pt dp-m)
(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT dp-f dp-pt dp-l))
(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT dp-g dp-pt dp-m))
(dsp-split!)

(define dp-pf (dsp-phi-for dp-pt dp-l))
(define dp-pg (dsp-phi-for dp-pt dp-m))
(define dp-hf (dsp-diffid dp-pf))
(define dp-hg (dsp-diffid dp-pg))
(define dp-fa (list dp-f dp-pt))                          ; f(a)
(define dp-k  (list 'VNB-LAMBDA 'x 'RR dp-fa))            ; K  = const f(a)
(define dp-p1 (list 'VNB-LAMBDA 'x 'RR (list '* (list dp-pf 'x) (list dp-g 'x))))
(define dp-p2 (list 'VNB-LAMBDA 'x 'RR (list '* (list dp-k 'x) (list dp-pg 'x))))
(define dp-w  (list 'VNB-LAMBDA 'x 'RR (list '+ (list dp-p1 'x) (list dp-p2 'x))))

(fact 'fun-apply-type-c dp-f 'RR 'RR dp-pt)               ; (IN f(a) RR)
(fact 'fun-apply-type-c dp-g 'RR 'RR dp-pt)               ; (IN g(a) RR)
(dsp-mul! dp-l (list dp-g dp-pt))
(dsp-mul! dp-fa dp-m)
(dsp-add! (list '* dp-l (list dp-g dp-pt)) (list '* dp-fa dp-m))
(fact 'const-lam-in-fun dp-fa)                            ; K is a function
(fact 'prod-lam-in-fun dp-f dp-g)                         ; the goal lambda
(fact 'prod-lam-in-fun dp-pf dp-g)                        ; P1
(fact 'prod-lam-in-fun dp-k dp-pg)                        ; P2
(fact 'sum-lam-in-fun dp-p1 dp-p2)                        ; W
(fact 'const-continuous-at dp-fa dp-pt)                   ; K continuous at a
(fact 'product-continuous-at dp-pf dp-g dp-pt)            ; P1 continuous at a
(fact 'product-continuous-at dp-k dp-pg dp-pt)            ; P2 continuous at a
(fact 'sum-continuous-at dp-p1 dp-p2 dp-pt)               ; W continuous at a

(mac 'IS-DIFF-AT)
(di) (ass)                                        ; lambda in FUN(RR,RR)
(di) (ass)                                        ; a in RR
(di) (ass)                                        ; L*g(a) + f(a)*M in RR
(ew dp-w)                                         ; phi := phi_f.g + f(a).phi_g
(di) (ass)                                        ; witness typing
(di) (ass)                                        ; witness continuity
(di) (dsp-beta!)                                  ; W(a) = phi_f(a)g(a) + f(a)phi_g(a)
(subst (list '= (list dp-pf dp-pt) dp-l))
(subst (list '= (list dp-pg dp-pt) dp-m))
(rfl)
;;; the factorization.  Distribute the RIGHT side so that phi_f(x)(x-a) and
;;; phi_g(x)(x-a) appear as subterms, replace each by the difference it equals,
;;; and the remainder -- f(x)g(x)-f(a)g(a) = (f(x)-f(a))g(x) + f(a)(g(x)-g(a)) --
;;; is exactly the add-and-subtract-f(a)g(x) identity, closed by `crs'.
(let ((z (cadr (car (dk-landed* (lambda () (di)))))))
  (dsp-beta!)
  (inst+ dp-hf z)                                 ; f(x)-f(a) = phi_f(x)(x-a)
  (inst+ dp-hg z)                                 ; g(x)-g(a) = phi_g(x)(x-a)
  (fact 'fun-apply-type-c dp-pf 'RR 'RR z)
  (fact 'fun-apply-type-c dp-pg 'RR 'RR z)
  (fact 'fun-apply-type-c dp-f 'RR 'RR z)
  (fact 'fun-apply-type-c dp-g 'RR 'RR z)
  (fact 'rr-sub-in-rr z dp-pt)
  (let* ((d  (list '- z dp-pt))
         (p  (list dp-pf z))
         (q  (list dp-pg z))
         (gx (list dp-g z))
         (fd (list '- (list dp-f z) dp-fa))
         (gd (list '- gx (list dp-g dp-pt)))
         (dist (list '= (list '* (list '+ (list '* p gx) (list '* dp-fa q)) d)
                        (list '+ (list '* (list '* p d) gx)
                                 (list '* dp-fa (list '* q d))))))
    (have! dist (lambda () (crs)))
    (subst dist)
    (fact 'eq-sym fd (list '* p d))
    (subst (list '= (list '* p d) fd))
    (fact 'eq-sym gd (list '* q d))
    (subst (list '= (list '* q d) gd))
    (crs)))
(qed 'deriv-product)
(topic! 'deriv-product 'analysis)
(alias! 'deriv-product "the Leibniz rule: (fg)' = f'g + fg'")
