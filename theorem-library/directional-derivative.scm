;;; directional-derivative.scm -- calculus.pdf Chapter 2 section 8 "Multivariable
;;; Calculus", Def 2.23 through Prop 2.27, over an arbitrary real normed vector
;;; space.
;;;
;;; THE DESIGN IS THE NOTES' OWN, and it is the whole point of the section:
;;; NOTHING here is a multivariable derivative.  Def 2.23 turns a direction into
;;; a CURVE,
;;;
;;;     f_{a,eta}(t)  =  f(a + t.eta)          SEG-CURVE(m, f, a, eta)
;;;
;;; which is a map RR -> RR, and every one of 2.24-2.27 is a statement about the
;;; ORDINARY one-variable Caratheodory derivative of that curve at 0:
;;;
;;;     d_eta f(a)    =  f'_{a,eta}(0)         DIR-DERIV(m, f, a, eta)
;;;
;;; So the existing 1-D machinery does all of the work: `mvt' (mvt-proof.scm)
;;; proves 2.24 and `deriv-chain' (chain-rule.scm) proves 2.25, exactly as the
;;; notes' own two proofs say ("By the Mean Value Theorem for functions on an
;;; interval", "by the Chain Rule for functions on an interval").
;;;
;;; THE ONE MECHANISM.  Both of those proofs are the same move -- reparametrise
;;; the segment affinely and read the derivative at 0 -- so it is proved ONCE,
;;; as `dir-diff-reparam':
;;;
;;;     F(t) == G(c + lam.t) pointwise,  G differentiable at c with G'(c)=dl
;;;        =>  F differentiable at 0 with F'(0) = dl * lam
;;;
;;; 2.25 is the instance c=0, lam=lambda; 2.24 is the instance c=theta, lam=1.
;;; It is proved from `deriv-chain' plus `diff-transfer-ptwise-eq', the
;;; IS-DIFF-AT analogue of `cont-transfer-ptwise-eq' proved here for the same
;;; reason that one exists: the chain rule concludes about the literal term
;;; COMPOSE(G, AF), and the curve actually in hand is some other term that
;;; agrees with it at every point.
;;;
;;; ====================================================================
;;; TWO HYPOTHESES OF THE NOTES ARE DROPPED, AND ONE DEFECT IS INHERITED.
;;; ====================================================================
;;;
;;; (1) NO OPEN SET U.  The notes state 2.23-2.29 for f real-valued on an OPEN
;;;     U subset E, with f_{a,eta} defined only on a small open segment (-r,r).
;;;     The tree has no metric SUBSPACE structure, so "f defined on an open
;;;     subset" is not expressible at all; this is the same wall the
;;;     neighbourhood form of the chain rule hits (see chain-rule.scm's
;;;     DISCREPANCY note) and it is a known open design fork.  So every
;;;     statement here is GLOBAL: f is total on VEC(m) (IN f (FUN (VEC m) RR)),
;;;     and f_{a,eta} is consequently total on RR.  Mathematically this is the
;;;     special case U = E of the notes; it is not a weakening of the proofs,
;;;     which never use openness for anything except to know the curve is
;;;     defined near the point.
;;;
;;; (2) NO NEIGHBOURHOOD IN 2.26.  The notes' Lemma 2.26 asks that d_eta f and
;;;     d_xi f exist and be continuous "in a neighborhood of a".  Same wall:
;;;     `dir-deriv-additive' below asks that they exist at EVERY point of
;;;     VEC(m) and are continuous at a (in the norm metric NVS-METRIC-SPACE).
;;;
;;; (3) IS-NORMED-VECTOR-SPACE WAS UNSATISFIABLE when this file landed, so --
;;;     as with every other theorem in the tree stated over it
;;;     (hahn-banach-proof.scm, norm-as-sup-proof.scm, vector-taylor-proof.scm,
;;;     dual-space.scm) -- the NVS-level results here were VACUOUS.
;;;     normed-vector-space.scm declared `(substructure SCAL RING)', whose
;;;     IS-RING conjunct pins length(SCAL s)=6, and then pinned
;;;     `scal(s) = rr-normed-field', a 7-tuple.  REPAIRED 2026-08-23: the
;;;     scalars are pinned through NORMED-FIELD-AS-COMMUTATIVE-RING, which
;;;     projects slots 1..6 into a fresh 6-tuple, and the predicate is
;;;     satisfiable.  No bill in this file moved -- nothing here unfolds the
;;;     predicate.
;;;
;;;     WHAT REMAINS is a different and weaker thing, and should not be confused
;;;     with the above: NORMED-VECTOR-SPACE has no INSTANCE anywhere in the tree,
;;;     so the NVS-level results are unexemplified.  That is an ordinary missing
;;;     construction (see "2.28 / 2.29 ARE NOT HERE" below -- R^n is what would
;;;     supply one), not a contradiction.
;;;
;;; ====================================================================
;;; 2.28 / 2.29 ARE NOT HERE.
;;; ====================================================================
;;; They need E = R^n concretely (a basis e_1..e_n and the sup norm
;;; ||eta|| = max|eta_i|), and there is no R^n in the tree: NORMED-VECTOR-SPACE
;;; has no instances and there is no sup-norm anywhere.  Building one is new
;;; vocabulary of real size and is a decision for the user; see the report.
;;;
;;; Loads after vector-taylor-proof (NVS-METRIC-SPACE), mvt-proof (mvt),
;;; chain-rule (deriv-chain, deriv-of-is-diff-at), differentiation (IS-DIFF-AT,
;;; DERIV), continuity-basics (const-lam-in-fun, const-continuous-at), compose
;;; (compose-apply, compose-type), number-systems (rr-*-closed), driver-kit.

;;; ---- file-local driver helpers (the `dd-' prefix) --------------------

(define (dd-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 24) (error "dd-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

(define (dd-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 24)) #t)
          ((and (pair? (car l)) (memq (caar l) '(AND FORSOME)))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (dd-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "dd-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; Walk a right-nested AND goal down to its leaves, running CLOSER on each.
(define (dd-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (dd-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; a real-arithmetic identity, proved by `crs' and landed in the context
(define (dd-arith! eqn) (have! eqn (lambda () (crs))))

;;; ====================================================================
;;; DEFINITION 2.23 -- the segment curve and the directional derivative
;;; ====================================================================

;;; f_{a,eta}(t) = f(a + t.eta), equation (36).  A map RR -> RR whatever f is.
(def-functoid 'SEG-CURVE '(m f a eta)
  '(VNB-LAMBDA u_ RR (f ((VADD m) a ((ACT m) u_ eta)))))

;;; d_eta f(a) exists and equals dl:  the CURVE is differentiable at 0.
;;; No extra typing conjuncts are needed -- IS-DIFF-AT already pins
;;; SEG-CURVE(...) in FUN(RR,RR), 0 in RR and dl in RR.
(def-predicate 'IS-DIR-DIFF-AT '(m f a eta dl)
  '(IS-DIFF-AT (SEG-CURVE m f a eta) 0 dl))

;;; d_eta f(a) itself, equation (37) read through the Caratheodory derivative.
(def-functoid 'DIR-DERIV '(m f a eta)
  '(DERIV (SEG-CURVE m f a eta) 0))

;;; ====================================================================
;;; THE VECTOR ALGEBRA THE SECTION USES.  Six read-offs of the
;;; NORMED-VECTOR-SPACE laws with the scalars written as reals -- which is the
;;; house idiom for an NVS (hahn-banach-proof.scm writes `(IN r_ RR)' and
;;; `((ACT m) r_ v)' side by side), justified by the structure's own law
;;; `scal(s) = normed-field-as-commutative-ring(rr-normed-field)'.  Each is one
;;; module axiom read through that pinning composed with the six read-offs of
;;; the ring view proved in theorem-library/normed-field-ring-view.scm; none is
;;; new mathematics, and each is therefore a candidate for PROOF rather than
;;; assertion -- see prove-scripts/drives/nvs-scalar-bridge-drive.scm.  They are the ONLY vector facts the whole
;;; section needs, and every one of 2.24-2.27 below reaches the vectors only
;;; through them.
;;; ====================================================================

(add-to-pss 'nvs-act-in-vec
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (IN ((ACT m) r_ x_) (VEC m)))))))))
(warrant! 'nvs-act-in-vec 'reference
  "Action closure, the shape conjunct ACT(m) in FUN(CARTESIAN(RR, VEC(m)), VEC(m))
   of IS-NORMED-VECTOR-SPACE read in applied form; module-act-type with the
   scalar carrier CARR(SCAL m) = RR -- the pinning scal(m) =
   normed-field-as-commutative-ring(rr-normed-field) composed with
   rr-scalar-ring-carr (theorem-library/normed-field-ring-view.scm).")
(topic! 'nvs-act-in-vec 'analysis)

;;; nvs-vadd-in-vec is PROVEN (2026-08-31) in theorem-library/op-typing.scm, with the
;;; other six applied-form op typings: one driver over the IS-X unfold plus
;;; apply-tupling-2 and fun-apply-type-c -- the derivation the warrant here
;;; recited.

;;; r.(s.x) = (r*s).x
(add-to-pss 'nvs-act-scale-assoc
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) r_ ((ACT m) s_ x_)) ((ACT m) (* r_ s_) x_)))))))))))
(warrant! 'nvs-act-scale-assoc 'reference
  "module-act-mul-compat, act(mul(scal)(r,s), x) = act(r, act(s,x)), with the
   scalars pinned to RR through the ring view of RR-NORMED-FIELD, so
   MUL(SCAL m) is bintimes (rr-scalar-ring-mul) and bintimes(r,s) = r*s by
   nary-times-2.")
(topic! 'nvs-act-scale-assoc 'analysis)

;;; (y + r.x) + s.x = y + (r+s).x
(add-to-pss 'nvs-act-collect
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) ((VADD m) y_ ((ACT m) r_ x_)) ((ACT m) s_ x_))
          ((VADD m) y_ ((ACT m) (+ r_ s_) x_))))))))))))))
(warrant! 'nvs-act-collect 'reference
  "Associativity of VADD (an abelian-group law of the structure) followed by
   module-act-distrib-scalar, act(add(scal)(r,s),x) = act(r,x) + act(s,x), with
   ADD(SCAL m) = binplus (rr-scalar-ring-add) and binplus(r,s) = r+s
   (nary-plus-2).")
(topic! 'nvs-act-collect 'analysis)

;;; y + 0.x = y
(add-to-pss 'nvs-act-zero
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) y_ ((ACT m) 0 x_)) y_))))))))
(warrant! 'nvs-act-zero 'reference
  "0.x = VZERO(m) (module-act-distrib-scalar at r=s=0 plus cancellation, the
   standard module fact), and VZERO is the VADD identity -- the
   `is-identity VADD VZERO VEC' property of the declaration.")
(topic! 'nvs-act-zero 'analysis)

;;; y + 1.x = y + x
(add-to-pss 'nvs-act-one
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) y_ ((ACT m) 1 x_)) ((VADD m) y_ x_)))))))))
(warrant! 'nvs-act-one 'reference
  "module-act-unital, act(one(scal(s)), x) = x, with ONE(SCAL m) = 1 --
   rr-scalar-ring-one, slot 6 of the ring view of the instance tuple.")
(topic! 'nvs-act-one 'analysis)

;;; ====================================================================
;;; THE ONE-VARIABLE MACHINERY.  Five results about maps RR -> RR; none
;;; mentions a vector space, and none is vacuous.
;;; ====================================================================

;;; (0) the beta law of the curve: SEG-CURVE(m,f,a,eta)(t) == f(a + t.eta).
;;; A functoid installs only a rewrite macete, so this equation has to exist as
;;; a THEOREM before `mac-h' can use it on a hypothesis -- and it is PROVABLE,
;;; `(di) (mac 'SEG-CURVE) (qrfl)', not something to assert.
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL t_
        (IMPLIES (IN t_ RR)
          (== ((SEG-CURVE m f a eta) t_)
              (f ((VADD m) a ((ACT m) t_ eta))))))))))))
(di)
(mac 'SEG-CURVE)
(lam-b)
(qrfl)
(qed 'seg-curve-apply)
(topic! 'seg-curve-apply 'analysis)
(alias! 'seg-curve-apply "the segment curve f_{a,eta} evaluated at t")

;;; (1) a Caratheodory witness is a function RR -> RR.  A one-line projection,
;;; needed because `mac-h' on IS-DIFF-AT would DELETE the hypothesis it unfolds.
(sp (make-wff
     '(FORALL f (FORALL a (FORALL dl
        (IMPLIES (IS-DIFF-AT f a dl) (IN f (FUN RR RR))))))))
(dd-peel-to! 'IN)
(mac-h 'IS-DIFF-AT (dd-find 'hyp (dk-head? 'IS-DIFF-AT)))
(dd-split!)
(ass)
(qed 'diff-at-in-fun)
(topic! 'diff-at-in-fun 'analysis)

;;; (2) the affine map x |-> c + lam*x is a function RR -> RR.
(sp (make-wff
     '(FORALL c (FORALL lam
        (IMPLIES (AND (IN c RR) (IN lam RR))
          (IN (VNB-LAMBDA x RR (+ c (* lam x))) (FUN RR RR)))))))
(dd-peel-to! 'IN)
(dd-split!)
(dk-lam-t!)
(let* ((land (dk-landed (lambda () (di))))
       (xv (cadr (car land))))
  (have! (list 'AND '(IN lam RR) (list 'IN xv 'RR)))
  (fact 'rr-mul-closed 'lam xv)
  (have! (list 'AND '(IN c RR) (list 'IN (list '* 'lam xv) 'RR)))
  (fact 'rr-add-closed 'c (list '* 'lam xv))
  (ass))
(qed 'affine-lam-in-fun)
(topic! 'affine-lam-in-fun 'analysis)

;;; (3) the derivative of the affine map x |-> c + lam*x is lam, everywhere.
;;; Witness phi = the constant lam: (c+lam*x) - (c+lam*a) = lam*(x-a) is a ring
;;; identity, so `crs' closes the factorization and `const-continuous-at' the
;;; only analytic obligation.  This is deriv-identity's proof with one constant.
(sp (make-wff
     '(FORALL c (FORALL lam (FORALL a
        (IMPLIES (AND (IN c RR) (AND (IN lam RR) (IN a RR)))
          (IS-DIFF-AT (VNB-LAMBDA x RR (+ c (* lam x))) a lam)))))))
(grind)
(have! '(AND (IN c RR) (IN lam RR)))
(mac 'IS-DIFF-AT)
(di)(fact 'affine-lam-in-fun 'c 'lam)(ass)         ; the map is RR -> RR
(di)(ass)                                          ; a in RR
(di)(ass)                                          ; lam in RR
(ew '(VNB-LAMBDA x RR lam))                        ; phi := the constant lam
(di)(fact 'const-lam-in-fun 'lam)(ass)
(di)(fact 'const-continuous-at 'lam 'a)(ass)
(di)(lam-b)(rfl)                                   ; phi(a) = lam
(di)(lam-b)(lam-b)(lam-b)(crs)                     ; the Caratheodory factorization
(qed 'deriv-affine)
(topic! 'deriv-affine 'analysis)
(alias! 'deriv-affine "the derivative of x |-> c + lam*x is lam")

;;; (4) `diff-transfer-ptwise-eq' -- differentiability reads only the VALUES --
;;; USED to be proved here.  MOVED 2026-08-23 to theorem-library/diff-transfer.scm,
;;; statement reproduced VERBATIM (the `==' hypothesis included), because the
;;; POWER RULE (theorem-library/deriv-power.scm) needs it and loads long before
;;; this file: without a transfer an induction cannot feed one rung's conclusion
;;; into the next, since `deriv-product' concludes about the literal lambda it
;;; builds.  Nothing else changed; `dir-diff-reparam' below still cites it by
;;; name, and this file's dependency on it is now a load-order fact rather than
;;; a local proof.
;;;
;;; The helper the moved block defined is kept here, because three later
;;; proofs use it: the universals in these contexts share the FORALL/IMPLIES
;;; shape and are told apart on the CONSEQUENT's head -- `==' for a pointwise
;;; hypothesis, `=' for a Caratheodory identity.
(define (dd-consequent-head? h)
  (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                    (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                    (pair? (caddr (caddr fm)))
                    (eq? (car (caddr (caddr fm))) h))))

;;; ====================================================================
;;; THE MECHANISM: affine reparametrisation of a curve.
;;;
;;;   F(t) == G(c + lam*t) for every real t,  G'(c) = dl
;;;      =>  F'(0) = dl * lam
;;;
;;; Proved ONCE.  Prop 2.24 is the instance (c := theta, lam := 1) and Lemma
;;; 2.25 is the instance (c := 0, lam := lambda); nothing else in the section
;;; touches the chain rule.  The affine map AF = x |-> c + lam*x supplies the
;;; inner factor, `deriv-chain' composes, and `diff-transfer-ptwise-eq' carries
;;; the conclusion from COMPOSE(G,AF) -- the term the chain rule talks about --
;;; to F, the term in hand.
;;; ====================================================================
(sp (make-wff
     '(FORALL f (FORALL g (FORALL c (FORALL lam (FORALL dl
        (IMPLIES (IN f (FUN RR RR))
        (IMPLIES (IN c RR)
        (IMPLIES (IN lam RR)
        (IMPLIES (IS-DIFF-AT g c dl)
        (IMPLIES (FORALL x_ (IMPLIES (IN x_ RR) (== (f x_) (g (+ c (* lam x_))))))
                 (IS-DIFF-AT f 0 (* dl lam))))))))))))))
(dd-peel-to! 'IS-DIFF-AT)
(define dd-rf (list-ref (dk-goal) 1))
(define dd-rg (list-ref (dd-find 'gdiff (dk-head? 'IS-DIFF-AT)) 1))
(define dd-rhyp (dd-find 'reparam (dd-consequent-head? '==)))
(define dd-af '(VNB-LAMBDA x RR (+ c (* lam x))))
(define dd-comp (list 'COMPOSE dd-rg dd-af))

(fact 'rr-zero-in)
(fact 'diff-at-in-fun dd-rg 'c 'dl)                       ; g : RR -> RR
(have! '(AND (IN c RR) (IN lam RR)))
(fact 'affine-lam-in-fun 'c 'lam)                         ; AF : RR -> RR
(have! '(AND (IN c RR) (AND (IN lam RR) (IN 0 RR))))
(fact 'deriv-affine 'c 'lam 0)                            ; AF'(0) = lam

;;; the chain rule wants g differentiable at AF(0), not at c: beta-reduce and
;;; rewrite by the ring identity c + lam*0 = c.
(dd-arith! '(= (+ c (* lam 0)) c))
(have! (list 'IS-DIFF-AT dd-rg (list dd-af 0) 'dl)
       (lambda () (lam-b) (subst '(= (+ c (* lam 0)) c)) (ass)))
(fact 'deriv-chain dd-af dd-rg 0 'lam 'dl)                ; (g o AF)'(0) = dl*lam

;;; F agrees pointwise with g o AF: compose-apply, then beta.
(have! (list 'AND (list 'IN dd-af '(FUN RR RR)) (list 'IN dd-rg '(FUN RR RR))))
(define dd-capply (dk-fact! 'compose-apply 'RR 'RR 'RR dd-rg dd-af))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dd-rf 'x_) (list dd-comp 'x_))))
       (lambda ()
         (let ((xv (cadr (car (dk-landed (lambda () (di)))))))
           (inst+ dd-capply xv)
           (subst (list '= (list dd-comp xv) (list dd-rg (list dd-af xv))))
           (lam-b)
           (inst+ dd-rhyp xv)
           (ass))))
(fact 'diff-transfer-ptwise-eq dd-rf dd-comp 0 '(* dl lam))
(ass)
(qed 'dir-diff-reparam)
(topic! 'dir-diff-reparam 'analysis)
(alias! 'dir-diff-reparam "affine reparametrisation of a differentiable curve")

;;; the value of a Caratheodory witness is a real (companion of diff-at-in-fun).
(sp (make-wff
     '(FORALL f (FORALL a (FORALL dl
        (IMPLIES (IS-DIFF-AT f a dl) (IN dl RR)))))))
(dd-peel-to! 'IN)
(mac-h 'IS-DIFF-AT (dd-find 'hyp (dk-head? 'IS-DIFF-AT)))
(dd-split!)
(ass)
(qed 'diff-at-value-in-rr)
(topic! 'diff-at-value-in-rr 'analysis)

;;; The two instances of the mechanism, isolated so that the vector-space
;;; drivers below never have to carry `(+ 0 ...)' or `(* dl 1)' around.
;;;   SCALE:  F(t) == G(lam*t)  =>  F'(0) = lam * G'(0)
;;;   SHIFT:  F(t) == G(c + t)  =>  F'(0) = G'(c)
(sp (make-wff
     '(FORALL f (FORALL g (FORALL lam (FORALL dl
        (IMPLIES (IN f (FUN RR RR))
        (IMPLIES (IN lam RR)
        (IMPLIES (IS-DIFF-AT g 0 dl)
        (IMPLIES (FORALL x_ (IMPLIES (IN x_ RR) (== (f x_) (g (* lam x_)))))
                 (IS-DIFF-AT f 0 (* lam dl))))))))))))
(dd-peel-to! 'IS-DIFF-AT)
(define dd-sf (list-ref (dk-goal) 1))
(define dd-sg (list-ref (dd-find 'gdiff (dk-head? 'IS-DIFF-AT)) 1))
(define dd-shyp (dd-find 'scale (dd-consequent-head? '==)))
(fact 'rr-zero-in)
(fact 'diff-at-value-in-rr dd-sg 0 'dl)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dd-sf 'x_) (list dd-sg '(+ 0 (* lam x_))))))
       (lambda ()
         (let ((xv (cadr (car (dk-landed (lambda () (di)))))))
           (dd-arith! (list '= (list '+ 0 (list '* 'lam xv)) (list '* 'lam xv)))
           (subst (list '= (list '+ 0 (list '* 'lam xv)) (list '* 'lam xv)))
           (inst+ dd-shyp xv)
           (ass))))
(fact 'dir-diff-reparam dd-sf dd-sg 0 'lam 'dl)
(dd-arith! '(= (* lam dl) (* dl lam)))
(subst '(= (* lam dl) (* dl lam)))
(ass)
(qed 'dir-diff-scale)
(topic! 'dir-diff-scale 'analysis)

(sp (make-wff
     '(FORALL f (FORALL g (FORALL c (FORALL dl
        (IMPLIES (IN f (FUN RR RR))
        (IMPLIES (IN c RR)
        (IMPLIES (IS-DIFF-AT g c dl)
        (IMPLIES (FORALL x_ (IMPLIES (IN x_ RR) (== (f x_) (g (+ c x_)))))
                 (IS-DIFF-AT f 0 dl)))))))))))
(dd-peel-to! 'IS-DIFF-AT)
(define dd-hf (list-ref (dk-goal) 1))
(define dd-hg (list-ref (dd-find 'gdiff (dk-head? 'IS-DIFF-AT)) 1))
(define dd-hhyp (dd-find 'shift (dd-consequent-head? '==)))
(fact 'rr-one-in)
(fact 'diff-at-value-in-rr dd-hg 'c 'dl)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dd-hf 'x_) (list dd-hg '(+ c (* 1 x_))))))
       (lambda ()
         (let ((xv (cadr (car (dk-landed (lambda () (di)))))))
           (dd-arith! (list '= (list '* 1 xv) xv))
           (subst (list '= (list '* 1 xv) xv))
           (inst+ dd-hhyp xv)
           (ass))))
(fact 'dir-diff-reparam dd-hf dd-hg 'c 1 'dl)
(dd-arith! '(= dl (* dl 1)))
(subst '(= dl (* dl 1)))
(ass)
(qed 'dir-diff-shift)
(topic! 'dir-diff-shift 'analysis)

;;; ====================================================================
;;; THE VECTOR-SPACE LAYER.  2.24 - 2.27.
;;; ====================================================================

;;; The segment curve is a real function of a real variable.  This is where the
;;; GLOBAL statement pays: f total on VEC(m) makes f_{a,eta} total on RR, which
;;; is what IS-DIFF-AT asks for and what the notes get instead from openness.
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL eta
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IN f (FUN (VEC m) RR))
        (IMPLIES (IN a (VEC m))
        (IMPLIES (IN eta (VEC m))
          (IN (SEG-CURVE m f a eta) (FUN RR RR))))))))))))
(dd-peel-to! 'IN)
(mac 'SEG-CURVE)
(dk-lam-t!)
(let ((xv (cadr (car (dk-landed (lambda () (di)))))))
  (fact 'nvs-act-in-vec 'm xv 'eta)
  (fact 'nvs-vadd-in-vec 'm 'a (list '(ACT m) xv 'eta))
  (fact 'fun-apply-type-c 'f '(VEC m) 'RR (list '(VADD m) 'a (list '(ACT m) xv 'eta)))
  (ass))
(qed 'seg-curve-in-fun)
(topic! 'seg-curve-in-fun 'analysis)

;;; --------------------------------------------------------------------
;;; LEMMA 2.25 -- homogeneity.   d_{lambda.eta} f(a) = lambda * d_eta f(a).
;;;
;;; The notes' proof is one sentence: f_{a,lambda.eta}(t) = f_{a,eta}(lambda t)
;;; "so that by the Chain Rule for functions on an interval,
;;;  f'_{a,lambda.eta}(0) = lambda f'_{a,eta}(0)".  That is `dir-diff-scale'
;;; verbatim; all that is left is the pointwise identity, and its whole vector
;;; content is one module axiom, t.(lambda.eta) = (t*lambda).eta.
;;; --------------------------------------------------------------------
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL lam (FORALL dl
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IN f (FUN (VEC m) RR))
        (IMPLIES (IN a (VEC m))
        (IMPLIES (IN eta (VEC m))
        (IMPLIES (IN lam RR)
        (IMPLIES (IS-DIR-DIFF-AT m f a eta dl)
          (IS-DIR-DIFF-AT m f a ((ACT m) lam eta) (* lam dl))))))))))))))))
(dd-peel-to! 'IS-DIR-DIFF-AT)
(define dd-hg2 '(SEG-CURVE m f a eta))
(define dd-le  '((ACT m) lam eta))
(define dd-hf2 (list 'SEG-CURVE 'm 'f 'a dd-le))
(mac-h 'IS-DIR-DIFF-AT (dd-find 'dirdiff (dk-head? 'IS-DIR-DIFF-AT)))
(fact 'nvs-act-in-vec 'm 'lam 'eta)
(fact 'seg-curve-in-fun 'm 'f 'a dd-le)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dd-hf2 'x_) (list dd-hg2 '(* lam x_)))))
       (lambda ()
         (let ((xv (cadr (car (dk-landed (lambda () (di)))))))
           (have! (list 'AND '(IN lam RR) (list 'IN xv 'RR)))
           (fact 'rr-mul-closed 'lam xv)
           (subst (dk-fact! 'seg-curve-apply 'm 'f 'a dd-le xv))
           (subst (dk-fact! 'seg-curve-apply 'm 'f 'a 'eta (list '* 'lam xv)))
           (subst (dk-fact! 'nvs-act-scale-assoc 'm xv 'lam 'eta))
           (dd-arith! (list '= (list '* 'lam xv) (list '* xv 'lam)))
           (subst (list '= (list '* 'lam xv) (list '* xv 'lam)))
           (qrfl))))
(mac 'IS-DIR-DIFF-AT)
(fact 'dir-diff-scale dd-hf2 dd-hg2 'lam 'dl)
(ass)
(qed 'dir-deriv-homogeneous)
(topic! 'dir-deriv-homogeneous 'analysis)
(alias! 'dir-deriv-homogeneous "the directional derivative is homogeneous in the direction")

;;; --------------------------------------------------------------------
;;; PROPOSITION 2.24 -- MEAN VALUE THEOREM, equation (38).
;;;
;;;     f(a + eta) - f(a)  =  d_eta f(a + theta.eta)     for some theta in (0,1)
;;;
;;; The notes' proof is: f_{a,eta} is defined on [0,1], the scalar MVT (Thm 2.13)
;;; gives theta in (0,1) with f_{a,eta}(1) - f_{a,eta}(0) = f'_{a,eta}(theta),
;;; and f'_{a,eta}(theta) = f'_{a+theta.eta,eta}(0) = d_eta f(a + theta.eta).
;;; That last step is the SHIFT instance of the mechanism; the two endpoint
;;; evaluations are 1.eta = eta and 0.eta = 0 (nvs-act-one / nvs-act-zero).
;;;
;;; The continuity/differentiability hypotheses are stated ON THE CURVE, exactly
;;; the form `mvt' consumes -- which is also the honest form: with no metric
;;; subspace in the tree there is no way to say "f is differentiable on an open
;;; U containing the segment", and saying it of the curve is what the notes'
;;; proof actually uses.
;;; --------------------------------------------------------------------
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL eta
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IN f (FUN (VEC m) RR))
        (IMPLIES (IN a (VEC m))
        (IMPLIES (IN eta (VEC m))
        (IMPLIES (FORALL x (IMPLIES (IN x (CCINT 0 1))
                    (IS-CONTINUOUS-AT RR-MS RR-MS (SEG-CURVE m f a eta) x)))
        (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< 0 x) (< x 1)))
                    (FORSOME L (IS-DIFF-AT (SEG-CURVE m f a eta) x L))))
          (FORSOME th (AND (IN th RR) (AND (< 0 th) (AND (< th 1)
            (FORSOME dv (AND (IS-DIR-DIFF-AT m f ((VADD m) a ((ACT m) th eta)) eta dv)
                             (= dv (- (f ((VADD m) a eta)) (f a)))))))))))))))))))))
(dd-peel-to! 'FORSOME)
(define dd-mg '(SEG-CURVE m f a eta))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'seg-curve-in-fun 'm 'f 'a 'eta)
(have! '(< 0 1) (lambda () (arith)))
(have! (list 'AND (list 'IN dd-mg '(FUN RR RR)) '(AND (IN 0 RR) (AND (IN 1 RR) (< 0 1)))))
(fact 'mvt dd-mg 0 1)
(dd-split!)
(define dd-mvthyp
  (dd-find 'mvt-witness
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'IS-DIFF-AT)
                      (equal? (cadr fm) dd-mg) (symbol? (caddr fm))))))
(define dd-th (caddr dd-mvthyp))
(define dd-dv (cadddr dd-mvthyp))
(define dd-at (list '(VADD m) 'a (list '(ACT m) dd-th 'eta)))
(define dd-mf (list 'SEG-CURVE 'm 'f dd-at 'eta))
(define dd-g1 (list dd-mg 1))
(define dd-g0 (list dd-mg 0))

;;; the shifted curve is a real function, and agrees pointwise with t |-> G(th+t)
(fact 'nvs-act-in-vec 'm dd-th 'eta)
(fact 'nvs-vadd-in-vec 'm 'a (list '(ACT m) dd-th 'eta))
(fact 'seg-curve-in-fun 'm 'f dd-at 'eta)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list dd-mf 'x_) (list dd-mg (list '+ dd-th 'x_)))))
       (lambda ()
         (let ((xv (cadr (car (dk-landed (lambda () (di)))))))
           (have! (list 'AND (list 'IN dd-th 'RR) (list 'IN xv 'RR)))
           (fact 'rr-add-closed dd-th xv)
           (subst (dk-fact! 'seg-curve-apply 'm 'f dd-at 'eta xv))
           (subst (dk-fact! 'seg-curve-apply 'm 'f 'a 'eta (list '+ dd-th xv)))
           (subst (dk-fact! 'nvs-act-collect 'm dd-th xv 'eta 'a))
           (qrfl))))

;;; the two endpoint evaluations:  G(1) == f(a+eta),  G(0) == f(a)
(fact 'nvs-act-one 'm 'eta 'a)
(fact 'nvs-act-zero 'm 'eta 'a)
(have! (list '== (list 'f '((VADD m) a eta)) dd-g1)
       (lambda ()
         (subst (dk-fact! 'seg-curve-apply 'm 'f 'a 'eta 1))
         (subst '(= ((VADD m) a ((ACT m) 1 eta)) ((VADD m) a eta)))
         (qrfl)))
(have! (list '== '(f a) dd-g0)
       (lambda ()
         (subst (dk-fact! 'seg-curve-apply 'm 'f 'a 'eta 0))
         (subst '(= ((VADD m) a ((ACT m) 0 eta)) a))
         (qrfl)))
(fact 'diff-at-value-in-rr dd-mg dd-th dd-dv)

;;; witness theta and the MVT's own derivative value
(ew dd-th)
(dd-goal-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORSOME)
       (begin
         (ew dd-dv)
         (dd-goal-and!
          (lambda ()
            (let ((h (dk-goal)))
              (cond
                ((eq? (car h) 'IS-DIR-DIFF-AT)
                 (mac 'IS-DIR-DIFF-AT)
                 (fact 'dir-diff-shift dd-mf dd-mg dd-th dd-dv)
                 (ass))
                ((eq? (car h) '=)
                 (subst (list '== (list 'f '((VADD m) a eta)) dd-g1))
                 (subst (list '== '(f a) dd-g0))
                 (fact 'eq-sym (list '* dd-dv '(- 1 0)) (list '- dd-g1 dd-g0))
                 (subst (list '= (list '- dd-g1 dd-g0) (list '* dd-dv '(- 1 0))))
                 (crs))
                (else (ass)))))))
       (ass))))
(qed 'dir-deriv-mvt)
(topic! 'dir-deriv-mvt 'analysis)
(alias! 'dir-deriv-mvt "the mean value theorem along a segment")

;;; DIR-DERIV reads the value off any witness (the DERIV corollary).
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL dl
        (IMPLIES (IS-DIR-DIFF-AT m f a eta dl)
                 (= (DIR-DERIV m f a eta) dl)))))))))
(dd-peel-to! '=)
(mac-h 'IS-DIR-DIFF-AT (dd-find 'hyp (dk-head? 'IS-DIR-DIFF-AT)))
(mac 'DIR-DERIV)
(fact 'deriv-of-is-diff-at '(SEG-CURVE m f a eta) 0 'dl)
(ass)
(qed 'dir-deriv-value)
(topic! 'dir-deriv-value 'analysis)
(alias! 'dir-deriv-value "DIR-DERIV is the value of any directional-derivative witness")

;;; --------------------------------------------------------------------
;;; LEMMA 2.26 -- additivity, equation (41).  ASSERTED.
;;;
;;;   d_{eta+xi} f(a) = d_eta f(a) + d_xi f(a)
;;;
;;; This is the ONE result of the section that is not a corollary of the
;;; one-variable theory, and the notes' proof says why: it is a genuine
;;; eps/delta argument in TWO parameters.  Given eps, choose delta so that the
;;; two increments
;;;      Delta_1(alpha,beta) = d_xi f(a + alpha.xi + beta.eta) - d_xi f(a)
;;;      Delta_2(alpha,beta) = d_eta f(a + alpha.xi + beta.eta) - d_eta f(a)
;;; are < eps for |alpha|,|beta| <= delta -- which is exactly the CONTINUITY
;;; hypothesis, and is the reason 2.26 needs one where 2.25 does not.  Then split
;;;      f(a + t.(xi+eta)) - f(a)
;;;         = [f(a + t.xi + t.eta) - f(a + t.xi)] + [f(a + t.xi) - f(a)]
;;; and apply Prop 2.24 (`dir-deriv-mvt') to each bracket, getting
;;;      = {d_eta f(a) + Delta_1(t, t.theta) + d_xi f(a) + Delta_2(t.rho, 0)} * t
;;; with |theta|,|rho| < 1, so that |t^{-1}(f(a+t.(xi+eta)) - f(a)) -
;;; d_eta f(a) - d_xi f(a)| <= 2 eps for |t| <= delta.  eps arbitrary gives the
;;; limit.
;;;
;;; WHY IT IS ASSERTED RATHER THAN PROVED, and this is a finding rather than an
;;; omission: the argument does not decompose into the mechanism above.  The
;;; two applications of 2.24 land at DIFFERENT base points (a + t.xi and a),
;;; the mean-value parameters theta and rho are produced by 2.24 and then have
;;; to be fed back into the continuity estimate as ARGUMENTS OF THE INCREMENT,
;;; and the conclusion is a limit statement about the difference quotient --
;;; which in the Caratheodory foundation means exhibiting a factor phi
;;; continuous at 0, i.e. the eps/delta work has to be redone as a continuity
;;; construction.  None of that is reparametrisation, and none of it is
;;; available as a rewrite.
;;;
;;; The hypotheses are the GLOBAL reading of the notes' "in a neighborhood of a"
;;; (see the header): the two directional derivatives exist at EVERY point of
;;; VEC(m), and x |-> d_eta f(x), x |-> d_xi f(x) are continuous at a in the
;;; norm metric NVS-METRIC-SPACE(m).
;;; --------------------------------------------------------------------
(add-to-pss 'dir-deriv-additive
  `(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL xi (FORALL dl (FORALL dm
     (IMPLIES ,(conjuncts->and
       '((IS-NORMED-VECTOR-SPACE m)
         (IN f (FUN (VEC m) RR))
         (IN a (VEC m))
         (IN eta (VEC m))
         (IN xi (VEC m))
         (IS-DIR-DIFF-AT m f a eta dl)
         (IS-DIR-DIFF-AT m f a xi dm)
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
            (FORSOME k_ (IS-DIR-DIFF-AT m f x_ eta k_))))
         (FORALL x_ (IMPLIES (IN x_ (VEC m))
            (FORSOME k_ (IS-DIR-DIFF-AT m f x_ xi k_))))
         (IS-CONTINUOUS-AT (NVS-METRIC-SPACE m) RR-MS
            (VNB-LAMBDA x_ (VEC m) (DIR-DERIV m f x_ eta)) a)
         (IS-CONTINUOUS-AT (NVS-METRIC-SPACE m) RR-MS
            (VNB-LAMBDA x_ (VEC m) (DIR-DERIV m f x_ xi)) a)))
       (IS-DIR-DIFF-AT m f a ((VADD m) eta xi) (+ dl dm)))))))))))
(warrant! 'dir-deriv-additive 'reference
  "calculus.pdf Lemma 2.26 (equation (41)), stated globally.  Given eps, the
   continuity of x |-> d_eta f(x) and x |-> d_xi f(x) at a supplies a delta with
   |d_xi f(a+alpha.xi+beta.eta) - d_xi f(a)| < eps and likewise for eta whenever
   |alpha|,|beta| <= delta.  Splitting f(a+t.(xi+eta)) - f(a) at the corner
   a + t.xi and applying the segment mean value theorem (Prop 2.24) to each
   bracket gives f(a+t.(xi+eta)) - f(a) = {d_eta f(a) + Delta_1(t,t.theta) +
   d_xi f(a) + Delta_2(t.rho,0)} * t with |theta|,|rho| < 1, so the difference
   quotient is within 2 eps of d_eta f(a) + d_xi f(a) for |t| <= delta; eps was
   arbitrary.")
(topic! 'dir-deriv-additive 'analysis)

;;; --------------------------------------------------------------------
;;; PROPOSITION 2.27 -- linearity of the direction.  PROVEN from 2.25 + 2.26,
;;; which is exactly what the notes say ("This is immediate from Lemmas 2.25
;;; and 2.26").
;;;
;;;     d_{r.eta + s.xi} f(a)  =  r d_eta f(a) + s d_xi f(a)
;;;
;;; The additivity hypotheses are carried at the SCALED directions r.eta and
;;; s.xi, because that is where 2.26 is applied; the notes hide this by
;;; quantifying over "phi in the vector space V generated by eta, xi", which is
;;; the same thing once 2.25 has moved the scalars out.
;;; --------------------------------------------------------------------
(define dd-re '((ACT m) r eta))
(define dd-sx '((ACT m) s xi))
(define dd-ex-re
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (VEC m))
        (list 'FORSOME 'k_ (list 'IS-DIR-DIFF-AT 'm 'f 'x_ dd-re 'k_)))))
(define dd-ex-sx
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (VEC m))
        (list 'FORSOME 'k_ (list 'IS-DIR-DIFF-AT 'm 'f 'x_ dd-sx 'k_)))))
(define dd-ct-re
  (list 'IS-CONTINUOUS-AT '(NVS-METRIC-SPACE m) 'RR-MS
        (list 'VNB-LAMBDA 'x_ '(VEC m) (list 'DIR-DERIV 'm 'f 'x_ dd-re)) 'a))
(define dd-ct-sx
  (list 'IS-CONTINUOUS-AT '(NVS-METRIC-SPACE m) 'RR-MS
        (list 'VNB-LAMBDA 'x_ '(VEC m) (list 'DIR-DERIV 'm 'f 'x_ dd-sx)) 'a))

(sp (make-wff
     `(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL xi (FORALL r (FORALL s (FORALL dl (FORALL dm
        (IMPLIES ,(conjuncts->and
                    '((IS-NORMED-VECTOR-SPACE m) (IN f (FUN (VEC m) RR))
                      (IN a (VEC m)) (IN eta (VEC m)) (IN xi (VEC m))
                      (IN r RR) (IN s RR)
                      (IS-DIR-DIFF-AT m f a eta dl)
                      (IS-DIR-DIFF-AT m f a xi dm)))
        (IMPLIES ,(conjuncts->and (list dd-ex-re dd-ex-sx dd-ct-re dd-ct-sx))
          (IS-DIR-DIFF-AT m f a ((VADD m) ((ACT m) r eta) ((ACT m) s xi))
                          (+ (* r dl) (* s dm))))))))))))))))
(dd-peel-to! 'IS-DIR-DIFF-AT)
(dd-split!)
(fact 'nvs-act-in-vec 'm 'r 'eta)
(fact 'nvs-act-in-vec 'm 's 'xi)
(fact 'dir-deriv-homogeneous 'm 'f 'a 'eta 'r 'dl)
(fact 'dir-deriv-homogeneous 'm 'f 'a 'xi 's 'dm)
(have! (conjuncts->and
         (list '(IS-NORMED-VECTOR-SPACE m) '(IN f (FUN (VEC m) RR)) '(IN a (VEC m))
               (list 'IN dd-re '(VEC m)) (list 'IN dd-sx '(VEC m))
               (list 'IS-DIR-DIFF-AT 'm 'f 'a dd-re '(* r dl))
               (list 'IS-DIR-DIFF-AT 'm 'f 'a dd-sx '(* s dm))
               dd-ex-re dd-ex-sx dd-ct-re dd-ct-sx)))
(fact 'dir-deriv-additive 'm 'f 'a dd-re dd-sx '(* r dl) '(* s dm))
(ass)
(qed 'dir-deriv-linear)
(topic! 'dir-deriv-linear 'analysis)
(alias! 'dir-deriv-linear "the directional derivative is linear in the direction")

;;; -----------------------------------------------------------------------
;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-DIR-DIFF-AT 'kind 'predicate 'arity 5
           'english "$2 has directional derivative $5 at $3 in the direction $4, in $1")
