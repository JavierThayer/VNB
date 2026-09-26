;;; chain-rule.scm -- THE CHAIN RULE (calculus.pdf Prop 2.8), PROVEN.
;;;
;;;   IS-DIFF-AT(f, a, L)  and  IS-DIFF-AT(g, f(a), M)
;;;      =>  IS-DIFF-AT(COMPOSE(g,f), a, M*L)
;;;
;;; and its DERIV corollary, deriv-chain-value:
;;;
;;;   DERIV(COMPOSE(g,f), a) = DERIV(g, f(a)) * DERIV(f, a)
;;;
;;; This was the `reference'-warranted support `deriv-chain' of
;;; theorem-library/differentiation.scm; the statement is reproduced VERBATIM
;;; from there, so any citation reads exactly as before.
;;;
;;; WHY IT IS CHEAP, and it is the whole argument for the Caratheodory
;;; foundation.  The notes prove Prop 2.8 in the o/O calculus (calculus.pdf
;;; p.16): expand g(f(a+h)) with f(a+h) = f(a) + f'(a)h + o(h), then absorb
;;; o_h(f'(a)h + o(h)) into o(h).  That absorption -- o of an o -- is the one
;;; step of the notes' proof with real content, and the tree has no o/O algebra
;;; to do it with.  In the Caratheodory form there is no h and no o at all:
;;;
;;;     f(x) - f(a)      =  phi(x) (x - a)          phi cont at a,   phi(a) = L
;;;     g(y) - g(f(a))   =  psi(y) (y - f(a))       psi cont at f(a), psi(f(a)) = M
;;;
;;; substitute y := f(x) in the second and the first into the result:
;;;
;;;     (g o f)(x) - (g o f)(a)  =  psi(f(x)) (f(x) - f(a))
;;;                              =  [psi(f(x)) phi(x)] (x - a)
;;;
;;; so the Caratheodory factor of g o f is chi = (psi o f) . phi, and its value
;;; at a is psi(f(a)) phi(a) = M L.  Two substitutions and one `crs' for the
;;; reassociation.  The ONLY analytic content left is that chi is continuous at
;;; a, and that is `product-continuous-at' applied to psi o f and phi -- psi o f
;;; being continuous at a by `compose-continuous-at'
;;; (theorem-library/continuity-compose.scm, PROVEN 2026-08-23) from f
;;; continuous at a (`diff-implies-continuous', modulo 0) and psi continuous at
;;; f(a).  No eps, no delta, no limit anywhere in this file.
;;;
;;; DISCREPANCY WITH THE NOTES, stated once: Prop 2.8 is about maps defined on
;;; NEIGHBOURHOODS U of a and V of f(a), and its equation (13) reads
;;; (g o f)'(a) = g'(f(a)) o f'(a) -- the composition of the two derivative
;;; MAPS, which at a real variable is their product.  IS-DIFF-AT is global
;;; (f in FUN(RR,RR)) and its derivative is the real number L, so the form
;;; proved here is the product.  The neighbourhood version needs a metric
;;; SUBSPACE structure, which the tree does not have.
;;;
;;; WHAT IT COSTS: `modulo {compose-type, compose-apply}' [trust: proof] --
;;; inherited entire from compose-continuous-at, and coming from the two
;;; COMPOSE laws of structure-library/compose.scm.  Both are `warrant! 'proof'
;;; supports whose warrant text IS a one-line derivation that has never been
;;; run; `compose-apply' looks reachable (unfold, land (IN x (DOM g)) off
;;; dom-fun-membership, `lam-b', `rfl'), `compose-type' less so -- `lam-t'
;;; types the unfolded lambda over (DOM g), and getting from there to FUN(A,C)
;;; wants `dom-of-fun', hence (IN A SET), which nothing in the tree derives
;;; from (IN g (FUN A B)).
;;;
;;; DRIVER NOTES.
;;;
;;; * `diff-implies-continuous' is cited BEFORE the two `mac-h' unfolds, not
;;;   after: `mac-h' REPLACES the assumption it unfolds, so unfolding
;;;   IS-DIFF-AT(f,a,L) deletes the hypothesis that citation needs.
;;; * The two Caratheodory factors are told apart by the POINT of their
;;;   continuity -- phi at a, psi at f(a) -- and phi additionally by not being
;;;   f, since f's own continuity (just landed) is also at a.
;;; * chi is not reconstructed by hand: `product-continuous-at' concludes about
;;;   the literal term (VNB-LAMBDA x RR (* (G x) (H x))), and that term, read
;;;   off the landing, IS the existential witness.  Reconstructing it would be
;;;   a second guess at the binder name.
;;; * `lam-b' needs its argument TYPED FIRST.  (IN a RR) and (IN x RR) are both
;;;   in the context before any beta step here; a beta fired without them owes
;;;   the typing at a node whose context predates the variable, and that leaf
;;;   cannot be closed.
;;;
;;; Loads after differentiation (IS-DIFF-AT, DERIV, diff-implies-continuous,
;;; derivative-unique) and continuity-compose (compose-continuous-at); needs
;;; continuity-product (product-continuous-at, prod-lam-in-fun), compose
;;; (compose-type, compose-apply), fun-apply-type-proof (fun-apply-type-c),
;;; number-systems (rr-mul-closed), driver-kit.

;;; ---- file-local driver helpers (the `chr-' prefix) --------------------

(define (chr-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 16) (error "chr-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

;;; split every conjunctive / existential assumption, skolemizing the FORSOME
;;; the IS-DIFF-AT unfold carries.
(define (chr-split!)
  (let loop ((budget 40))
    (when (> budget 0)
      (let ((tgt (let scan ((as (dk-asms)))
                   (cond ((null? as) #f)
                         ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                         (else (scan (cdr as)))))))
        (when tgt (ai tgt) (loop (- budget 1)))))))

;;; Project a typing conjunct out of an IS-DIFF-AT hypothesis H without
;;; destroying it: IS-DIFF-AT(f,a,L) is (IN f (FUN RR RR)) and (IN a RR) and
;;; (IN L RR) and ..., so the unfold + a split + `ass' closes any of the three.
;;; `mac-h' REPLACES the assumption it unfolds, so the unfold runs on the side
;;; branch of a `have!' and the main branch keeps H intact.  No-op when the
;;; typing is already in context (a `have!' of a context formula self-loops).
(define (chr-diff-typ! h t X)
  (if (not (any-pred (lambda (a) (equal? a (list 'IN t X))) (dk-asms)))
      (have! (list 'IN t X)
             (lambda () (mac-h 'IS-DIFF-AT h) (chr-split!) (ass)))))

(define (chr-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "chr-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; Walk a right-nested AND goal down to its leaves, running CLOSER on each.
(define (chr-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (chr-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (chr-has-redex? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (chr-has-redex? (car g)) (chr-has-redex? (cdr g))))
        (else #f)))

(define (chr-beta!)
  (let loop ((fuel 8))
    (if (and (> fuel 0) (chr-has-redex? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; ---- the eigenvariables and the constructed terms ---------------------

(define chr-f #f)     ; the inner map
(define chr-g #f)     ; the outer map
(define chr-a #f)     ; the point
(define chr-l #f)     ; f'(a)
(define chr-m #f)     ; g'(f(a))
(define chr-phi #f)   ; Caratheodory factor of f at a
(define chr-psi #f)   ; Caratheodory factor of g at f(a)
(define chr-psif #f)  ; COMPOSE(psi, f)
(define chr-gf #f)    ; COMPOSE(g, f)
(define chr-chi #f)   ; the witness (psi o f) . phi
(define chr-ap-gf #f)   ; forall x in RR. (COMPOSE(g,f))(x) = g(f(x))
(define chr-ap-psif #f) ; forall x in RR. (COMPOSE(psi,f))(x) = psi(f(x))
(define chr-id-f #f)    ; f's Caratheodory identity
(define chr-id-g #f)    ; g's Caratheodory identity

;;; the continuity assumption whose SUBJECT is not SKIP and whose POINT is PT
(define (chr-cont-at pt skip)
  (list-ref (chr-find 'cont
              (lambda (fm) (and (pair? fm) (eq? (car fm) 'IS-CONTINUOUS-AT)
                                (equal? (list-ref fm 4) pt)
                                (not (equal? (list-ref fm 3) skip)))))
            3))

;;; the Caratheodory identity mentioning the factor FAC: a FORALL whose body's
;;; consequent is an EQUATION.  Discriminated on the consequent, not on a
;;; symbol it contains -- compose-apply's landings are FORALL/= too, hence the
;;; extra test that the right-hand side is a PRODUCT.
(define (chr-identity fac)
  (chr-find 'identity
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                      (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                      (pair? (caddr (caddr fm)))
                      (eq? (car (caddr (caddr fm))) '=)
                      (pair? (caddr (caddr (caddr fm))))
                      (eq? (car (caddr (caddr (caddr fm)))) '*)
                      (dk-contains? fm fac)))))

;;; ---- the two goal branches under the witness --------------------------

;;; chi(a) = M*L
(define (chr-value!)
  (chr-beta!)                                     ; (psi o f)(a) * phi(a) = M*L
  (inst+ chr-ap-psif chr-a)
  (subst (list '= (list chr-psif chr-a) (list chr-psi (list chr-f chr-a))))
  (subst (list '= (list chr-psi (list chr-f chr-a)) chr-m))
  (subst (list '= (list chr-phi chr-a) chr-l))
  (rfl))

;;; (g o f)(x) - (g o f)(a) = chi(x) * (x - a)
(define (chr-identity!)
  (let* ((landed (dk-landed (lambda () (di))))
         (mem (or (find-first (lambda (u) (and (pair? u) (eq? (car u) 'IN))) landed)
                  (error "chr-identity!: no typing landed")))
         (x (cadr mem))
         (fx (list chr-f x)))
    (chr-beta!)                                   ; chi(x) -> (psi o f)(x) * phi(x)
    ;; name the three composite values
    (inst+ chr-ap-gf x)
    (inst+ chr-ap-gf chr-a)
    (inst+ chr-ap-psif x)
    (subst (list '= (list chr-gf x) (list chr-g fx)))
    (subst (list '= (list chr-gf chr-a) (list chr-g (list chr-f chr-a))))
    (subst (list '= (list chr-psif x) (list chr-psi fx)))
    ;; the two Caratheodory identities, at f(x) and at x
    (fact 'fun-apply-type-c chr-f 'RR 'RR x)      ; IN (f x) RR -- BEFORE the inst+
    (inst+ chr-id-g fx)
    (inst+ chr-id-f x)
    (subst (list '= (list '- (list chr-g fx) (list chr-g (list chr-f chr-a)))
                    (list '* (list chr-psi fx)
                             (list '- fx (list chr-f chr-a)))))
    (subst (list '= (list '- fx (list chr-f chr-a))
                    (list '* (list chr-phi x) (list '- x chr-a))))
    ;; ... leaving one reassociation
    (fact 'fun-apply-type-c chr-psi 'RR 'RR fx)
    (fact 'fun-apply-type-c chr-phi 'RR 'RR x)
    (crs)))

;;; ---- the proof -------------------------------------------------------

;;; Statement reproduced VERBATIM from theorem-library/differentiation.scm,
;;; where it stood as a `reference' support until 2026-08-23.
(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
        (IMPLIES (IS-DIFF-AT f a L)
        (IMPLIES (IS-DIFF-AT g (f a) M)
          (IS-DIFF-AT (COMPOSE g f) a (* M L)))))))))))
(chr-peel-to! 'IS-DIFF-AT)

(let* ((g0 (dk-goal))                             ; (IS-DIFF-AT (COMPOSE g f) a (* M L))
       (comp (list-ref g0 1))
       (prod (list-ref g0 3)))
  (set! chr-g (list-ref comp 1))
  (set! chr-f (list-ref comp 2))
  (set! chr-a (list-ref g0 2))
  (set! chr-m (list-ref prod 1))
  (set! chr-l (list-ref prod 2))
  (set! chr-gf comp))

;;; f is continuous at a -- cited BEFORE the unfold that would delete the
;;; IS-DIFF-AT hypothesis it needs.
(fact 'diff-implies-continuous chr-f chr-a chr-l)

(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT chr-f chr-a chr-l))
(chr-split!)
(mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT chr-g (list chr-f chr-a) chr-m))
(chr-split!)

(set! chr-phi (chr-cont-at chr-a chr-f))
(set! chr-psi (chr-cont-at (list chr-f chr-a) #f))
(set! chr-psif (list 'COMPOSE chr-psi chr-f))
(set! chr-id-f (chr-identity chr-phi))
(set! chr-id-g (chr-identity chr-psi))

;;; the two composites: typing and beta law.  `fact' will not split a
;;; conjunctive antecedent, so each AND goes into the context first.
;; compose-type is GUARDED on (IN A SET) since 2026-08-23; A = RR here.
(fact 'rr-is-set)
(have! (list 'AND (list 'IN chr-f '(FUN RR RR)) (list 'IN chr-psi '(FUN RR RR))))
(fact 'compose-type 'RR 'RR 'RR chr-psi chr-f)
(set! chr-ap-psif (dk-fact! 'compose-apply 'RR 'RR 'RR chr-psi chr-f))
(have! (list 'AND (list 'IN chr-f '(FUN RR RR)) (list 'IN chr-g '(FUN RR RR))))
(fact 'compose-type 'RR 'RR 'RR chr-g chr-f)
(set! chr-ap-gf (dk-fact! 'compose-apply 'RR 'RR 'RR chr-g chr-f))

;;; psi o f is continuous at a; chi = (psi o f).phi is continuous at a, is a
;;; function, and IS the witness -- read off the landing, not rebuilt.
(fact 'compose-continuous-at chr-psi chr-f chr-a)
(fact 'prod-lam-in-fun chr-psif chr-phi)
(set! chr-chi (list-ref (dk-fact! 'product-continuous-at chr-psif chr-phi chr-a) 3))

;;; M*L is a real
(have! (list 'AND (list 'IN chr-m 'RR) (list 'IN chr-l 'RR)))
(fact 'rr-mul-closed chr-m chr-l)

(mac 'IS-DIFF-AT)
(chr-goal-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORSOME)
            (ew chr-chi)
            (chr-goal-and!
             (lambda ()
               (let ((h (dk-goal)))
                 (cond ((eq? (car h) '=) (chr-value!))
                       ((eq? (car h) 'FORALL) (chr-identity!))
                       (else (ass)))))))
           (else (ass))))))

(qed 'deriv-chain)
(topic! 'deriv-chain 'analysis)
(alias! 'deriv-chain "the chain rule")

;;; =====================================================================
;;; The DERIV form -- calculus.pdf equation (13).
;;;
;;; DERIV(f,a) is IOTA L. IS-DIFF-AT(f,a,L) (differentiation.scm:48), so
;;; reading a value out of it is `iota-d': one leaf for existence-and-
;;; uniqueness and one for the goal with the defining property in hand.  Both
;;; are closed by `derivative-unique' (differentiation.scm, PROVEN), which is
;;; what makes the description well-formed in the first place.
;;;
;;; The universals are spelled `dv' / `dl' / `dm' and NOT L / M: DERIV's own
;;; IOTA binds `L', and an eigenvariable of that name would meet the binder the
;;; unfold introduces.  (VNB and MIT Scheme both fold case, so `L' and `l' are
;;; one name too.)
;;; =====================================================================

;;; L1.  Reading the derivative off a Caratheodory witness.
(sp (make-wff
     '(FORALL f (FORALL a (FORALL dv
        (IMPLIES (IS-DIFF-AT f a dv) (= (DERIV f a) dv)))))))
(chr-peel-to! '=)
(let* ((fh (chr-find 'hyp (lambda (u) (and (pair? u) (eq? (car u) 'IS-DIFF-AT)))))
       (df (list-ref fh 1)) (pt (list-ref fh 2)) (vl (list-ref fh 3)))
  (mac 'DERIV)
  (let ((iot (cadr (dk-goal))))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORSOME)
           ;; existence and uniqueness of the derivative at a
           (begin
             (ew vl)
             (chr-goal-and!
              (lambda ()
                (if (eq? (car (dk-goal)) 'FORALL)
                    (let* ((landed (dk-landed (lambda () (di) (di))))
                           (other (list-ref
                                   (or (find-first
                                        (lambda (u) (and (pair? u) (eq? (car u) 'IS-DIFF-AT)))
                                        landed)
                                       (error "L1: no second IS-DIFF-AT landed"))
                                   3)))
                      (have! (list 'AND (list 'IS-DIFF-AT df pt vl)
                                        (list 'IS-DIFF-AT df pt other)))
                      (fact 'derivative-unique df pt vl other)
                      (ass))
                    (ass)))))
           ;; the main branch: the description satisfies IS-DIFF-AT, so it is vl
           (begin
             ;; LUTINS instantiation (2026-09-18): `fact' at the DESCRIPTION
             ;; IOT owes (= iot iot) unless the context certifies it.  An IOTA
             ;; is never certified syntactically, so land its typing off the
             ;; property `iota-d' just granted -- (IN L RR) is the third
             ;; conjunct of IS-DIFF-AT.  In a `have!' LANE, because `mac-h'
             ;; REPLACES the hypothesis the `fact' below still needs.
             (chr-diff-typ! (list 'IS-DIFF-AT df pt iot) iot 'RR)
             (have! (list 'AND (list 'IS-DIFF-AT df pt iot)
                               (list 'IS-DIFF-AT df pt vl)))
             (fact 'derivative-unique df pt iot vl)
             (ass))))
     (dk-opened (lambda () (iota-d iot))))))
(qed 'deriv-of-is-diff-at)
(topic! 'deriv-of-is-diff-at 'analysis)
(alias! 'deriv-of-is-diff-at "DERIV(f,a) is the derivative of any Caratheodory witness")

;;; L2.  The chain rule as an equation between derivatives -- equation (13).
(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (FORALL dl (FORALL dm
        (IMPLIES (IS-DIFF-AT f a dl)
        (IMPLIES (IS-DIFF-AT g (f a) dm)
          (= (DERIV (COMPOSE g f) a) (* (DERIV g (f a)) (DERIV f a))))))))))))
(chr-peel-to! '=)
(let* ((g2 (dk-goal))
       (comp (cadr (cadr g2)))                    ; (COMPOSE g f)
       (gg (list-ref comp 1))
       (ff (list-ref comp 2))
       (pt (caddr (cadr g2)))                     ; a
       (hf (chr-find 'hyp-f
             (lambda (u) (and (pair? u) (eq? (car u) 'IS-DIFF-AT)
                              (equal? (list-ref u 1) ff)))))
       (hg (chr-find 'hyp-g
             (lambda (u) (and (pair? u) (eq? (car u) 'IS-DIFF-AT)
                              (equal? (list-ref u 1) gg)))))
       (dl (list-ref hf 3))
       (dm (list-ref hg 3)))
  ;; LUTINS instantiation (2026-09-18).  The three `deriv-of-is-diff-at'
  ;; citations below instantiate at dl, dm, (dm*dl) and at the point f(a);
  ;; the products and the application are certified only once their typings
  ;; are in the context, and all three come out of the IS-DIFF-AT
  ;; hypotheses (conjuncts 3 and 2).  `mac-h' is destructive, so each
  ;; projection runs on the side branch of a `have!' only.
  (chr-diff-typ! hf dl 'RR)
  (chr-diff-typ! hg dm 'RR)
  (chr-diff-typ! hg (list ff pt) 'RR)
  (have! (list 'IN (list '* dm dl) 'RR) (lambda () (in-rr)))
  (fact 'deriv-chain ff gg pt dl dm)               ; IS-DIFF-AT(g o f, a, dm*dl)
  (fact 'deriv-of-is-diff-at comp pt (list '* dm dl))
  (fact 'deriv-of-is-diff-at ff pt dl)
  (fact 'deriv-of-is-diff-at gg (list ff pt) dm)
  (subst (list '= (list 'DERIV ff pt) dl))
  (subst (list '= (list 'DERIV gg (list ff pt)) dm))
  (ass))
(qed 'deriv-chain-value)
(topic! 'deriv-chain-value 'analysis)
(alias! 'deriv-chain-value "the chain rule, as an equation between derivatives")
