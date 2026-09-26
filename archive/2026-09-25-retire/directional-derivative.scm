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
;;; RETIRED 2026-09-14 (proven): nvs-act-in-vec -- theorem-library/nvs-act-laws.scm
;;; RETIRED 2026-09-14 (proven): nvs-act-scale-assoc -- theorem-library/nvs-act-laws.scm
;;; RETIRED 2026-09-14 (proven): nvs-act-collect -- theorem-library/nvs-act-laws.scm
;;; RETIRED 2026-09-14 (proven): nvs-act-zero -- theorem-library/nvs-act-laws.scm
;;; RETIRED 2026-09-14 (proven): nvs-act-one -- theorem-library/nvs-act-laws.scm

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

;;; LUTINS instantiation (2026-09-18).  A `fact' AT a derivative VALUE owes
;;; (= t t) unless the context types the value, and the typing is a conjunct of
;;; the IS-DIFF-AT hypothesis that names it.  `mac-h' REPLACES the assumption it
;;; unfolds, so the unfold runs on a `have!' side branch and the main branch
;;; keeps the hypothesis the citation still needs.  No-op when the typing is
;;; already there (a `have!' of a context formula self-loops).
(define (dd-diff-typ! hyp t X)
  (if (not (any-pred (lambda (x) (equal? x (list 'IN t X))) (dk-asms)))
      (have! (list 'IN t X)
             (lambda () (mac-h 'IS-DIFF-AT hyp) (dd-split!) (ass)))))
;;; ... and the same one level up: IS-DIR-DIFF-AT(m,f,a,eta,dl) is
;;; IS-DIFF-AT(SEG-CURVE(m,f,a,eta), 0, dl) by definition, so two unfolds.
(define (dd-dirval-real! m f a eta dl)
  (if (not (any-pred (lambda (x) (equal? x (list 'IN dl 'RR))) (dk-asms)))
      (have! (list 'IN dl 'RR)
        (lambda ()
          (mac-h 'IS-DIR-DIFF-AT (list 'IS-DIR-DIFF-AT m f a eta dl))
          (mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT (list 'SEG-CURVE m f a eta) 0 dl))
          (dd-split!) (ass)))))

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


;;; nvs-vadd-in-vec is PROVEN (2026-08-31) in theorem-library/op-typing.scm, with the
;;; other six applied-form op typings: one driver over the IS-X unfold plus
;;; apply-tupling-2 and fun-apply-type-c -- the derivation the warrant here
;;; recited.

;;; r.(s.x) = (r*s).x

;;; (y + r.x) + s.x = y + (r+s).x

;;; y + 0.x = y

;;; y + 1.x = y + x

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
(define dd-rghyp (dd-find 'gdiff (dk-head? 'IS-DIFF-AT)))
(define dd-rg (list-ref dd-rghyp 1))
(define dd-rhyp (dd-find 'reparam (dd-consequent-head? '==)))
(define dd-af '(VNB-LAMBDA x RR (+ c (* lam x))))
(define dd-comp (list 'COMPOSE dd-rg dd-af))

(fact 'rr-zero-in)
(fact 'diff-at-in-fun dd-rg 'c 'dl)                       ; g : RR -> RR
;; LUTINS instantiation (2026-09-18): `diff-transfer-ptwise-eq' is cited below
;; AT the derivative value dl*lam, so both factors have to be typed first --
;; lam is a guarded binder, dl is the third conjunct of the IS-DIFF-AT
;; hypothesis.
(dd-diff-typ! dd-rghyp 'dl 'RR)
(have! '(IN (* dl lam) RR) (lambda () (in-rr)))
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

;;; the value of a Caratheodory witness is a real (companion of diff-at-in-fun)
;;; was proven here as `diff-at-value-in-rr'; REMOVED 2026-09-20 (batch 11,
;;; proven-duplicate-audit): it was alpha-equal to `diff-value-real'
;;; (theorem-library/mvt-cluster-readoffs.scm:78), which loads before this
;;; file.  The five citations below name that one.

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
(fact 'diff-value-real dd-sg 0 'dl)
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
(fact 'diff-value-real dd-hg 'c 'dl)
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
(fact 'diff-value-real dd-mg dd-th dd-dv)

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
;;; PROVEN on 2026-09-19 (rake batch 7-F; the spliced block below).  The paragraph
;;; that follows was written while the lemma was ASSERTED and is kept because it
;;; predicted the cost exactly: the Caratheodory factor is built and totalised
;;; by hand (dir-quotient-in-fun / -at-zero / -identity / -continuous).
;;; WHY IT WAS ASSERTED: the argument does not decompose into the mechanism above.  The
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
;;; ---- SPLICE BEGIN 2026-09-19 (rake batch 7-F) ----------------------
;;; The `add-to-pss' / `warrant!' / `topic!' of dir-deriv-additive that stood
;;; here are RETIRED: the lemma is proven below, `modulo 0'.  The block is
;;; theorem-library/rake-dir-deriv-additive.scm verbatim; its load window was
;;; EMPTY (asserted here, cited at the proof of `dir-deriv-linear' below), so
;;; it is spliced rather than wired as a file of its own.

;;; rake-dir-deriv-additive.scm -- LEMMA 2.26 of docs/calculus.pdf, additivity
;;; of the directional derivative, PROVEN.  Rake batch 7, assignment 7-F.
;;;
;;;   d_{eta+xi} f(a) = d_eta f(a) + d_xi f(a)
;;;
;;; Twenty-five theorems, every one `modulo 0'; the last is `dir-deriv-additive'
;;; itself, whose statement is copied LITERALLY from the `add-to-pss' it retires
;;; (theorem-library/directional-derivative.scm:650-668) -- the probe prints
;;; "re-installing the same statement".
;;;
;;; LOAD WINDOW: EMPTY.  `dir-deriv-additive' is asserted at
;;; directional-derivative.scm:650 and cited at :739 by `dir-deriv-linear', in
;;; that same file, and every lemma this proof needs (SEG-CURVE, IS-DIR-DIFF-AT,
;;; DIR-DERIV, seg-curve-apply, seg-curve-in-fun, dir-deriv-mvt, dir-deriv-value,
;;; dir-deriv-homogeneous) is defined in it above :650.  So this block is SPLICED
;;; into directional-derivative.scm in place of the add-to-pss / warrant! /
;;; topic! at :650-679, not wired as a file of its own.
;;;
;;; NOT PROVED HERE, and cited instead: `nvs-vadd-comm' and `nvs-act-distrib-vec'
;;; (the carrier-binder form), both installed by theorem-library/
;;; rake-hb-submodules.scm (batch 7-B), which loads before this file.
;;; install-duplicate-audit stays at zero.
;;;
;;; THE ROUTE.  The conclusion is IS-DIFF-AT(SEG-CURVE(m,f,a,eta+xi), 0, dl+dm),
;;; and the Caratheodory foundation asks for a factor phi continuous at 0.  There
;;; is no difference-quotient characterisation of the derivative in the tree
;;; (theorem-library/diff-at-local.scm says so in its header), so the factor is
;;; BUILT, by the totalising IF that file uses:
;;;
;;;     psi(z) = IF z = 0 THEN dl+dm ELSE (F(z) - F(0)) * recip(z)
;;;
;;; with F = SEG-CURVE(m,f,a,eta+xi).  The Caratheodory identity then holds by
;;; construction and the whole content is the CONTINUITY of psi at 0, which is
;;; the notes' eps/delta argument:
;;;
;;;   F(t) - F(0) = [f(a + t.xi + t.eta) - f(a + t.xi)] + [f(a + t.xi) - f(a)]
;;;               = t * (d_eta f(p1) + d_xi f(p2))
;;;
;;; with p1 = a + t.xi + (th*t).eta and p2 = a + (rh*t).xi produced by the segment
;;; mean value theorem (Prop 2.24, `dir-deriv-mvt'), 0 < th, rh < 1.  So
;;; psi(t) = d_eta f(p1) + d_xi f(p2) for t /= 0, and the continuity hypotheses on
;;; x |-> d_eta f(x), x |-> d_xi f(x) at a give |psi(t) - dl - dm| <= eps once
;;; d(a,p1), d(a,p2) <= the two deltas, which holds for
;;; |t| <= min(delta1,delta2) / (1 + ||eta|| + ||xi||) because
;;;    d(a, a + w) = ||w||   and   ||t.xi + u.eta|| <= |t|.||xi|| + |u|.||eta||.
;;;
;;; WHAT HAD TO BE BUILT FIRST (sections 1-9), none of it in the tree:
;;;   1. the norm/metric bricks of a normed vector space -- commutativity of
;;;      VADD, the inverse law, distributivity of the action over VADD, the
;;;      TRIANGLE and HOMOGENEITY laws of VNRM (projections of the
;;;      IS-NORMED-VECTOR-SPACE unfold, nvs-act-laws.scm's `nal-project!'
;;;      pattern), the distance of NVS-METRIC-SPACE and d(a, a+w) = ||w||;
;;;   2. `diff-at-shift-back', the converse of `dir-diff-shift': a derivative at 0
;;;      of the shifted curve is a derivative of the curve AT the shift.  This is
;;;      what turns "d_eta f exists at every point" into "the segment curve is
;;;      differentiable at every real", which is what Prop 2.24 consumes;
;;;   3. `dir-deriv-increment', Prop 2.24 with its two hypotheses discharged from
;;;      the global existence hypothesis and with the mean value read as
;;;      t * d_eta f(p) (homogeneity + `dir-deriv-value');
;;;   4. `dir-deriv-corner-split', the corner decomposition with both mean-value
;;;      points EXHIBITED and their distance to a bounded by |t| * (1 + ||eta|| +
;;;      ||xi||), and the two norm estimates that bound costs;
;;;   5. the Caratheodory factor PSI, its typing, its value at 0, the identity it
;;;      satisfies by construction, and (section 9) its CONTINUITY at 0 -- the
;;;      notes' eps/delta argument, and the only part that is not algebra.
;;;
;;; Helper prefix: `r8f-'.
;;; =====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define r8f-nvs '(IS-NORMED-VECTOR-SPACE m))

(define (r8f-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8f-nvs)
  (dk-split-all!))

(define (r8f-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-dir-deriv-additive: proof did not close" name
             (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;; the innermost consequent of a FORALL/IMPLIES tower
(define (r8f-core fm)
  (cond ((and (pair? fm) (eq? (car fm) 'FORALL)) (r8f-core (caddr fm)))
        ((and (pair? fm) (eq? (car fm) 'IMPLIES)) (r8f-core (caddr fm)))
        (#t fm)))

(define (r8f-eigen! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (v)
                (if (not (memq v fv))
                    (error "rake-dir-deriv-additive: eigenvariable not in goal" v
                           (expression->string (dk-goal)))))
              vars)))

;; A law of the IS-NORMED-VECTOR-SPACE unfold, instantiated at the goal's
;; eigenvariables and closed by `ass'.  FIND picks the law by its CONSEQUENT.
(define (r8f-project! name stmt find vars)
  (r8f-open! stmt)
  (r8f-eigen! vars)
  (let ((law (dk-pick (lambda (fm) (find (r8f-core fm))) name)))
    (apply dk-apply! law vars)
    (ass))
  (r8f-check! name))

;; (IN r (CARR (SCAL m))) from (IN r RR), by nvs-act-laws.scm's carrier read-off
(define (r8f-scalar! r)
  (have! (list 'IN r '(CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

;;; =====================================================================
;;; 1.  THE METRIC BRICKS
;;;
;;; The VECTOR and NORM bricks that stood here were MOVED on 2026-09-19 (rake
;;; batch 8, assignment 8-K1) to theorem-library/nvs-act-laws.scm
;;; (nvs-vneg-right, nvs-act-distrib-vec-rr) and theorem-library/
;;; nvs-norm-laws.scm (nvs-vnrm-triangle, nvs-vnrm-homog-c, nvs-vnrm-homog),
;;; both of which load far above this file; they are CITED below under the same
;;; names.  `nvs-vadd-comm' and `nvs-act-distrib-vec' were always cited, never
;;; proved here.  The two METRIC laws `nvs-metric-distance' (d(u,v) = ||u (-) v||)
;;; and `nvs-dist-shift' (d(u, u+w) = ||w||) FOLLOWED THEM on 2026-09-20 (batch
;;; 12-A), into theorem-library/nvs-norm-laws.scm: what had held them here was
;;; that NVS-METRIC-SPACE was a def-functoid of theorem-library/vector-taylor-proof
;;; and nvs-metric-is-ms of theorem-library/rake-norm-metrics.  The functoid is
;;; now structure-library/nvs-metric and rake-norm-metrics loads above
;;; nvs-norm-laws, so both laws load far above this file; they are CITED below
;;; under the same names.
;;; =====================================================================

;;; =====================================================================
;;; 2.  diff-at-shift-back -- the converse of `dir-diff-shift'.
;;;
;;;     g(x) == f(c + x) for every real x,  g'(0) = dl   =>   f'(c) = dl
;;;
;;; `dir-diff-reparam' reads a derivative AT 0 off one at c; this reads one at c
;;; off one at 0, and it is what turns "the directional derivative exists at
;;; every point" into "the segment curve is differentiable at every real" -- the
;;; shape Prop 2.24 consumes.  Same mechanism: the affine map AF(x) = -c + x
;;; supplies the inner factor, `deriv-chain' composes at c (AF(c) = 0), and
;;; `diff-transfer-ptwise-eq' carries the conclusion from COMPOSE(g,AF) to f.
;;; =====================================================================

(define (r8f-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "rake-dir-deriv-additive: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;; a universal told apart by the head of its CONSEQUENT
(define (r8f-cons-head? h)
  (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                    (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                    (pair? (caddr (caddr fm)))
                    (eq? (car (caddr (caddr fm))) h))))

;; walk a right-nested AND goal down to its leaves, running CLOSER on each
(define (r8f-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (r8f-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (r8f-di-var!)
  (cadr (car (dk-landed (lambda () (di))))))

;; `di' on an UNGUARDED universal lands nothing (CLAUDE.md), so a lane whose
;; hypothesis is a bare conjunction peels by GOAL HEAD rather than by count.
(define (r8f-to-head! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 8) (error "r8f-to-head!: never reached" head
                          (expression->string (dk-goal))))
          (#t (di) (loop (+ n 1))))))

(define r8f-af '(VNB-LAMBDA x RR (+ (- 0 c) (* 1 x))))
(define r8f-comp (list 'COMPOSE 'g r8f-af))

(sp (make-wff
     '(FORALL f (FORALL g (FORALL c (FORALL dl
        (IMPLIES (IN f (FUN RR RR))
        (IMPLIES (IN c RR)
        (IMPLIES (IS-DIFF-AT g 0 dl)
        (IMPLIES (FORALL x_ (IMPLIES (IN x_ RR) (== (g x_) (f (+ c x_)))))
                 (IS-DIFF-AT f c dl)))))))))))
(dk-peel!)
(define r8f-sb-hyp (r8f-find "the pointwise shift" (r8f-cons-head? '==)))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 'c)
(fact 'diff-value-real 'g 0 'dl)
(fact 'diff-at-in-fun 'g 0 'dl)
(have! '(AND (IN (- 0 c) RR) (IN 1 RR)))
(fact 'affine-lam-in-fun '(- 0 c) 1)
(have! '(AND (IN (- 0 c) RR) (AND (IN 1 RR) (IN c RR))))
(fact 'deriv-affine '(- 0 c) 1 'c)                  ; AF'(c) = 1
(have! '(= (+ (- 0 c) (* 1 c)) 0) (lambda () (crs)))
(have! (list 'IS-DIFF-AT 'g (list r8f-af 'c) 'dl)   ; g is differentiable at AF(c)
       (lambda () (lam-b) (subst '(= (+ (- 0 c) (* 1 c)) 0)) (ass)))
(fact 'deriv-chain r8f-af 'g 'c 1 'dl)              ; (g o AF)'(c) = dl*1
(have! (list 'AND (list 'IN r8f-af '(FUN RR RR)) '(IN g (FUN RR RR))))
(define r8f-capply (dk-fact! 'compose-apply 'RR 'RR 'RR 'g r8f-af))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== '(f x_) (list r8f-comp 'x_))))
       (lambda ()
         (let* ((xv (r8f-di-var!))
                (arg (list '+ '(- 0 c) (list '* 1 xv))))
           (inst+ r8f-capply xv)
           (subst (list '= (list r8f-comp xv) (list 'g (list r8f-af xv))))
           (lam-b)                                  ; goal: (== (f xv) (g arg))
           (have! (list 'IN arg 'RR) (lambda () (in-rr)))
           (inst+ r8f-sb-hyp arg)                   ; (== (g arg) (f (c + arg)))
           (subst (list '== (list 'g arg) (list 'f (list '+ 'c arg))))
           (have! (list '= (list '+ 'c arg) xv) (lambda () (crs)))
           (subst (list '= (list '+ 'c arg) xv))
           (fact 'fun-apply-type-c 'f 'RR 'RR xv)
           (qrfl))))
(fact 'diff-transfer-ptwise-eq 'f r8f-comp 'c '(* dl 1))
(have! '(= dl (* dl 1)) (lambda () (crs)))
(subst '(= dl (* dl 1)))
(ass)
(r8f-check! 'diff-at-shift-back)
(alias! 'diff-at-shift-back "a derivative of the shifted curve at 0 is a derivative at the shift")

;;; =====================================================================
;;; 3.  seg-curve-diff-at -- the directional derivative at a point of the
;;; segment IS the derivative of the curve at the corresponding parameter.
;;; The pointwise identity is `nvs-act-collect', exactly as in Prop 2.24.
;;; =====================================================================

(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL b_ (IMPLIES (IN b_ (VEC m))
     (FORALL eta (IMPLIES (IN eta (VEC m))
     (FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL k_ (IMPLIES (IS-DIR-DIFF-AT m f ((VADD m) b_ ((ACT m) s_ eta)) eta k_)
       (IS-DIFF-AT (SEG-CURVE m f b_ eta) s_ k_)))))))))))))))
(dk-peel!)
(define r8f-B '((VADD m) b_ ((ACT m) s_ eta)))
(define r8f-G (list 'SEG-CURVE 'm 'f r8f-B 'eta))
(define r8f-F '(SEG-CURVE m f b_ eta))
(mac-h 'IS-DIR-DIFF-AT (list 'IS-DIR-DIFF-AT 'm 'f r8f-B 'eta 'k_))
(fact 'nvs-act-in-vec 'm 's_ 'eta)
(fact 'nvs-vadd-in-vec 'm 'b_ '((ACT m) s_ eta))
(fact 'seg-curve-in-fun 'm 'f 'b_ 'eta)
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list r8f-G 'x_) (list r8f-F (list '+ 's_ 'x_)))))
       (lambda ()
         (let ((xv (r8f-di-var!)))
           (have! (list 'AND '(IN s_ RR) (list 'IN xv 'RR)))
           (fact 'rr-add-closed 's_ xv)
           (subst (dk-fact! 'seg-curve-apply 'm 'f r8f-B 'eta xv))
           (subst (dk-fact! 'seg-curve-apply 'm 'f 'b_ 'eta (list '+ 's_ xv)))
           (subst (dk-fact! 'nvs-act-collect 'm 's_ xv 'eta 'b_))
           (qrfl))))
(fact 'diff-at-shift-back r8f-F r8f-G 's_ 'k_)
(ass)
(r8f-check! 'seg-curve-diff-at)
(alias! 'seg-curve-diff-at "the segment curve is differentiable where the directional derivative exists")

;;; =====================================================================
;;; 4.  dir-deriv-increment -- Prop 2.24 with its two curve hypotheses
;;; discharged from "d_zeta f exists at every point", and the mean value read
;;; as a DIR-DERIV rather than as an existential witness.
;;; =====================================================================

;; split every conjunctive / existential assumption
(define (r8f-split-all!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 24)) #t)
          ((and (pair? (car l)) (memq (caar l) '(AND FORSOME)))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (#t (loop (cdr l) n)))))

(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL b_ (IMPLIES (IN b_ (VEC m))
     (FORALL zeta (IMPLIES (IN zeta (VEC m))
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (FORSOME k_ (IS-DIR-DIFF-AT m f x_ zeta k_))))
       (FORSOME th (AND (IN th RR) (AND (< 0 th) (AND (< th 1)
         (= (- (f ((VADD m) b_ zeta)) (f b_))
            (DIR-DERIV m f ((VADD m) b_ ((ACT m) th zeta)) zeta)))))))))))))))))
(dk-peel!)
(define r8f-ex (r8f-find "global existence" (r8f-cons-head? 'FORSOME)))
(define r8f-cv (list 'SEG-CURVE 'm 'f 'b_ 'zeta))
(fact 'seg-curve-in-fun 'm 'f 'b_ 'zeta)

;;; (a) the curve is differentiable at EVERY real
(define r8f-everywhere
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
        (list 'FORSOME 'L_ (list 'IS-DIFF-AT r8f-cv 'x_ 'L_)))))
(have! r8f-everywhere
  (lambda ()
    (let ((xv (r8f-di-var!)))
      (fact 'nvs-act-in-vec 'm xv 'zeta)
      (fact 'nvs-vadd-in-vec 'm 'b_ (list '(ACT m) xv 'zeta))
      (let* ((inst (dk-deepest
                    (lambda () (inst+ r8f-ex (list '(VADD m) 'b_ (list '(ACT m) xv 'zeta))))))
             (sk (dk-landed-1 (lambda () (ai inst))))
             (kv (list-ref sk 5)))
        (ew kv)
        (fact 'seg-curve-diff-at 'm 'f 'b_ 'zeta xv kv)
        (ass)))))

;;; (b) hence continuous on [0,1] ...
(have! (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT 0 1))
             (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS r8f-cv 'x)))
  (lambda ()
    (let* ((xv (r8f-di-var!))
           (mem (list 'AND (list 'IN xv 'RR)
                      (list 'AND (list '<= 0 xv) (list '<= xv 1)))))
      (fact 'ccint-membership 0 1 xv)
      (ai (list 'IFF (list 'IN xv '(CCINT 0 1)) mem))
      (detach! (list 'IMPLIES (list 'IN xv '(CCINT 0 1)) mem))
      (dk-split-all! (list mem))
      (let* ((inst (dk-deepest (lambda () (inst+ r8f-everywhere xv))))
             (sk (dk-landed-1 (lambda () (ai inst))))
             (lv (list-ref sk 3)))
        (fact 'diff-implies-continuous r8f-cv xv lv)
        (ass)))))

;;; ... and differentiable on (0,1), in the shape `mvt' consumes
(have! (list 'FORALL 'x (list 'IMPLIES
             (list 'AND '(IN x RR) (list 'AND '(< 0 x) '(< x 1)))
             (list 'FORSOME 'L (list 'IS-DIFF-AT r8f-cv 'x 'L))))
  (lambda ()
    (let* ((conj (car (dk-landed (lambda () (r8f-to-head! 'FORSOME)))))
           (xv (cadr (cadr conj))))
      (dk-split-all! (list conj))
      (let* ((inst (dk-deepest (lambda () (inst+ r8f-everywhere xv))))
             (sk (dk-landed-1 (lambda () (ai inst))))
             (lv (list-ref sk 3)))
        (ew lv)
        (ass)))))

;;; (c) Prop 2.24, and the witness value read as a DIR-DERIV
(fact 'dir-deriv-mvt 'm 'f 'b_ 'zeta)
(r8f-split-all!)
(define r8f-dveq
  (r8f-find "the mean value"
    (lambda (fm) (and (pair? fm) (eq? (car fm) '=)
                      (equal? (caddr fm)
                              (list '- (list 'f '((VADD m) b_ zeta)) '(f b_)))))))
(define r8f-dv (cadr r8f-dveq))
(define r8f-wit
  (r8f-find "the mvt witness"
    (lambda (fm) (and (pair? fm) (eq? (car fm) 'IS-DIR-DIFF-AT)
                      (= (length fm) 6) (equal? (list-ref fm 5) r8f-dv)))))
(define r8f-P (list-ref r8f-wit 3))
(ew (cadr (caddr r8f-P)))
(r8f-and!
 (lambda ()
   (if (eq? (car (dk-goal)) '=)
       (begin
         (fact 'dir-deriv-value 'm 'f r8f-P 'zeta r8f-dv)
         (subst (list '= (list 'DIR-DERIV 'm 'f r8f-P 'zeta) r8f-dv))
         (fact 'eq-sym r8f-dv (list '- (list 'f '((VADD m) b_ zeta)) '(f b_)))
         (ass))
       (ass))))
(r8f-check! 'dir-deriv-increment)
(alias! 'dir-deriv-increment "the segment mean value theorem, read as a directional derivative")

;;; the value of a directional derivative is a real (the IS-DIR-DIFF-AT
;;; companion of `diff-value-real'; the LUTINS rule wants it before any
;;; instantiation AT such a value)
(sp (make-wff
  '(FORALL m (FORALL f (FORALL a (FORALL eta (FORALL dl
     (IMPLIES (IS-DIR-DIFF-AT m f a eta dl) (IN dl RR)))))))))
(dk-peel!)
(mac-h 'IS-DIR-DIFF-AT '(IS-DIR-DIFF-AT m f a eta dl))
(fact 'diff-value-real '(SEG-CURVE m f a eta) 0 'dl)
(ass)
(r8f-check! 'dir-diff-value-in-rr)

;;; =====================================================================
;;; 5.  dir-deriv-increment-scaled -- the same with the direction scaled by t,
;;; and the mean value read as t * d_zeta f(p).  Homogeneity moves the scalar
;;; out on both sides; the mean-value point is b + (th*t).zeta.
;;; =====================================================================

(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL b_ (IMPLIES (IN b_ (VEC m))
     (FORALL zeta (IMPLIES (IN zeta (VEC m))
     (FORALL t_ (IMPLIES (IN t_ RR)
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ (VEC m))
                 (FORSOME k_ (IS-DIR-DIFF-AT m f x_ zeta k_))))
       (FORSOME th (AND (IN th RR) (AND (< 0 th) (AND (< th 1)
         (= (- (f ((VADD m) b_ ((ACT m) t_ zeta))) (f b_))
            (* t_ (DIR-DERIV m f ((VADD m) b_ ((ACT m) (* th t_) zeta)) zeta))))))))))))))))))))
(dk-peel!)
(define r8f-ex2 (r8f-find "global existence" (r8f-cons-head? 'FORSOME)))
(define r8f-tz '((ACT m) t_ zeta))
(fact 'nvs-act-in-vec 'm 't_ 'zeta)
;;; the derivative in the SCALED direction exists at every point too
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (VEC m))
             (list 'FORSOME 'k_ (list 'IS-DIR-DIFF-AT 'm 'f 'x_ r8f-tz 'k_))))
  (lambda ()
    (let* ((xv (r8f-di-var!))
           (inst (dk-deepest (lambda () (inst+ r8f-ex2 xv))))
           (sk (dk-landed-1 (lambda () (ai inst))))
           (kv (list-ref sk 5)))
      (fact 'dir-diff-value-in-rr 'm 'f xv 'zeta kv)
      (have! (list 'IN (list '* 't_ kv) 'RR) (lambda () (in-rr)))
      (ew (list '* 't_ kv))
      (fact 'dir-deriv-homogeneous 'm 'f xv 'zeta 't_ kv)
      (ass))))
(fact 'dir-deriv-increment 'm 'f 'b_ r8f-tz)
(r8f-split-all!)
(define r8f-inc2
  (r8f-find "the scaled mean value"
    (lambda (fm) (and (pair? fm) (eq? (car fm) '=)
                      (equal? (cadr fm)
                              (list '- (list 'f (list '(VADD m) 'b_ r8f-tz)) '(f b_)))))))
(define r8f-P0 (list-ref (caddr r8f-inc2) 3))
(define r8f-th0 (cadr (caddr r8f-P0)))
(ew r8f-th0)
(r8f-and!
 (lambda ()
   (if (eq? (car (dk-goal)) '=)
       (begin
         (fact 'nvs-act-scale-assoc 'm r8f-th0 't_ 'zeta)
         (fact 'eq-sym (list '(ACT m) r8f-th0 r8f-tz)
                       (list '(ACT m) (list '* r8f-th0 't_) 'zeta))
         (subst (list '= (list '(ACT m) (list '* r8f-th0 't_) 'zeta)
                         (list '(ACT m) r8f-th0 r8f-tz)))
         (fact 'nvs-act-in-vec 'm r8f-th0 r8f-tz)
         (fact 'nvs-vadd-in-vec 'm 'b_ (list '(ACT m) r8f-th0 r8f-tz))
         (let* ((inst (dk-deepest (lambda () (inst+ r8f-ex2 r8f-P0))))
                (sk (dk-landed-1 (lambda () (ai inst))))
                (kv (list-ref sk 5)))
           (fact 'dir-deriv-value 'm 'f r8f-P0 'zeta kv)
           (subst (list '= (list 'DIR-DERIV 'm 'f r8f-P0 'zeta) kv))
           (fact 'dir-diff-value-in-rr 'm 'f r8f-P0 'zeta kv)
           (fact 'dir-deriv-homogeneous 'm 'f r8f-P0 'zeta 't_ kv)
           (fact 'dir-deriv-value 'm 'f r8f-P0 r8f-tz (list '* 't_ kv))
           (fact 'eq-trans (cadr r8f-inc2) (caddr r8f-inc2) (list '* 't_ kv))
           (ass)))
       (ass))))
(r8f-check! 'dir-deriv-increment-scaled)

;;; =====================================================================
;;; 6.  THE TWO NORM ESTIMATES the mean-value points need.
;;;
;;; NOTE ON `ineq' (this cost a probe): the oracle DROPS a premise that is not
;;; linear in RR, and a product of two non-constant terms -- |c| * ||v|| -- is
;;; exactly that.  Every estimate below therefore chains by hand through
;;; `rr-leq-transitive' / `rr-le-add' / `rr-mul-le-right', with the products as
;;; opaque terms, and `ineq' is not used on them at all.
;;; =====================================================================

;; `ineq' by FORMULA rather than by index (premise indices are 1-based and
;; positional; naming the formulas is what keeps a long context honest)
(define (r8f-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rake-dir-deriv-additive: premise not in context"
                            (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r8f-ineq . forms) (apply ineq (map r8f-idx forms)))

(define (r8f-real! t)                  ; land (IN t RR)
  (if (not (any-pred (lambda (x) (equal? x (list 'IN t 'RR))) (dk-asms)))
      (have! (list 'IN t 'RR) (lambda () (in-rr)))))

(define (r8f-occurs? sub e)
  (cond ((equal? sub e) #t)
        ((pair? e) (or (r8f-occurs? sub (car e)) (r8f-occurs? sub (cdr e))))
        (#t #f)))

(define (r8f-eq-le! b c)               ; (= b c) in context  =>  (<= b c)
  ;; `subst' rewrites EVERY occurrence, so the side that CONTAINS the other has
  ;; to be the one rewritten away -- `x = 0 + (0 + x)' loops the other way round.
  (if (r8f-occurs? c b)
      (begin (r8f-real! c)
             (have! (list '<= b c)
                    (lambda () (subst (list '= b c))
                            (fact 'rr-leq-reflexive c) (ass))))
      (begin (r8f-real! b)
             (have! (list '<= b c)
                    (lambda () (subst (list '= c b))
                            (fact 'rr-leq-reflexive b) (ass))))))

(define (r8f-le-trans! a b c)          ; (<= a b), (<= b c)  =>  (<= a c)
  (for-each r8f-real! (list a b c))
  (have! (list 'AND (list 'IN a 'RR) (list 'AND (list 'IN b 'RR) (list 'IN c 'RR))))
  (have! (list 'AND (list '<= a b) (list '<= b c)))
  (fact 'rr-leq-transitive a b c))

(define (r8f-le-add! a b u v)          ; (<= a b), (<= u v)  =>  (<= (+ a u) (+ b v))
  (for-each r8f-real! (list a b u v))
  (have! (list 'AND (list '<= a b) (list '<= u v)))
  (fact 'rr-le-add a b u v))

(define (r8f-le-refl! a)               ; (<= a a)
  (r8f-real! a)
  (fact 'rr-leq-reflexive a))

;;; |s*t| <= |t| for 0 < s < 1 -- the mean-value parameter never enlarges the step
(sp (make-wff
  '(FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL t_ (IMPLIES (IN t_ RR)
       (IMPLIES (< 0 s_) (IMPLIES (< s_ 1)
         (<= (abs (* s_ t_)) (abs t_))))))))))
(dk-peel!)
(fact 'rr-abs-closed 't_)
(fact 'rr-abs-nonneg 't_)
(have! '(AND (IN s_ RR) (IN t_ RR)))      ; rr-abs-mult's antecedent is a CONJUNCTION
(fact 'rr-abs-mult 's_ 't_)
(fact 'rr-lt-implies-le 0 's_)
(fact 'rr-lt-implies-le 's_ 1)
(fact 'rr-abs-of-nonneg 's_)
(fact 'rr-mul-le-right 's_ 1 '(abs t_))
(have! '(= (* 1 (abs t_)) (abs t_)) (lambda () (crs)))
(subst '(= (abs (* s_ t_)) (* (abs s_) (abs t_))))
(subst '(= (abs s_) s_))
(r8f-eq-le! '(* 1 (abs t_)) '(abs t_))
(r8f-le-trans! '(* s_ (abs t_)) '(* 1 (abs t_)) '(abs t_))
(ass)
(r8f-check! 'rr-abs-unit-scale)

;;; ||c1.v1 (+) c2.v2|| <= bd * (1 + ||v2|| + ||v1||)  when |c1|, |c2| <= bd
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL v1 (IMPLIES (IN v1 (VEC m))
     (FORALL v2 (IMPLIES (IN v2 (VEC m))
     (FORALL c1 (IMPLIES (IN c1 RR)
     (FORALL c2 (IMPLIES (IN c2 RR)
     (FORALL bd (IMPLIES (IN bd RR)
       (IMPLIES (<= 0 bd)
       (IMPLIES (<= (abs c1) bd)
       (IMPLIES (<= (abs c2) bd)
         (<= ((VNRM m) ((VADD m) ((ACT m) c1 v1) ((ACT m) c2 v2)))
             (* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1))))))))))))))))))))))
(dk-peel!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(fact 'nvs-act-in-vec 'm 'c1 'v1)
(fact 'nvs-act-in-vec 'm 'c2 'v2)
(fact 'vnrm-real 'm 'v1) (fact 'vnrm-real 'm 'v2)
(fact 'vnrm-nonneg 'm 'v1) (fact 'vnrm-nonneg 'm 'v2)
(fact 'nvs-vadd-in-vec 'm '((ACT m) c1 v1) '((ACT m) c2 v2))
(fact 'vnrm-real 'm '((VADD m) ((ACT m) c1 v1) ((ACT m) c2 v2)))
(fact 'vnrm-real 'm '((ACT m) c1 v1)) (fact 'vnrm-real 'm '((ACT m) c2 v2))
(fact 'nvs-vnrm-triangle 'm '((ACT m) c1 v1) '((ACT m) c2 v2))
(fact 'nvs-vnrm-homog 'm 'c1 'v1)
(fact 'nvs-vnrm-homog 'm 'c2 'v2)
(fact 'rr-abs-closed 'c1) (fact 'rr-abs-closed 'c2)
(fact 'rr-mul-le-right '(abs c1) 'bd '((VNRM m) v1))
(fact 'rr-mul-le-right '(abs c2) 'bd '((VNRM m) v2))
(define r8f-2tsum '(+ (* bd ((VNRM m) v2)) (* bd ((VNRM m) v1))))
(have! (list '= '(* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1))))
                (list '+ 'bd r8f-2tsum))
       (lambda () (crs)))
(subst (list '= '(* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1))))
                (list '+ 'bd r8f-2tsum)))
;; goal:  ||c1.v1 + c2.v2||  <=  bd + (bd*||v2|| + bd*||v1||)
(have! '(<= ((VNRM m) ((VADD m) ((ACT m) c1 v1) ((ACT m) c2 v2)))
            (+ (* (abs c1) ((VNRM m) v1)) (* (abs c2) ((VNRM m) v2))))
  (lambda ()
    ;; used BACKWARDS: the goal carries the products, the triangle law the norms
    (subst '(= (* (abs c1) ((VNRM m) v1)) ((VNRM m) ((ACT m) c1 v1))))
    (subst '(= (* (abs c2) ((VNRM m) v2)) ((VNRM m) ((ACT m) c2 v2))))
    (ass)))
(r8f-le-add! '(* (abs c1) ((VNRM m) v1)) '(* bd ((VNRM m) v1))
             '(* (abs c2) ((VNRM m) v2)) '(* bd ((VNRM m) v2)))
(have! (list '= '(+ (* bd ((VNRM m) v1)) (* bd ((VNRM m) v2)))
                (list '+ 0 r8f-2tsum))
       (lambda () (crs)))
(r8f-eq-le! '(+ (* bd ((VNRM m) v1)) (* bd ((VNRM m) v2)))
            (list '+ 0 r8f-2tsum))
(r8f-le-refl! r8f-2tsum)
(r8f-le-add! 0 'bd r8f-2tsum r8f-2tsum)
(r8f-le-trans! '(+ (* bd ((VNRM m) v1)) (* bd ((VNRM m) v2)))
               (list '+ 0 r8f-2tsum)
               (list '+ 'bd r8f-2tsum))
(r8f-le-trans! '(+ (* (abs c1) ((VNRM m) v1)) (* (abs c2) ((VNRM m) v2)))
               '(+ (* bd ((VNRM m) v1)) (* bd ((VNRM m) v2)))
               (list '+ 'bd r8f-2tsum))
(r8f-le-trans! '((VNRM m) ((VADD m) ((ACT m) c1 v1) ((ACT m) c2 v2)))
               '(+ (* (abs c1) ((VNRM m) v1)) (* (abs c2) ((VNRM m) v2)))
               (list '+ 'bd r8f-2tsum))
(ass)
(r8f-check! 'nvs-norm-two-term-bound)

;;; ||c.v1|| <= bd * (1 + ||v2|| + ||v1||)  when |c| <= bd
(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL v1 (IMPLIES (IN v1 (VEC m))
     (FORALL v2 (IMPLIES (IN v2 (VEC m))
     (FORALL c1 (IMPLIES (IN c1 RR)
     (FORALL bd (IMPLIES (IN bd RR)
       (IMPLIES (<= 0 bd)
       (IMPLIES (<= (abs c1) bd)
         (<= ((VNRM m) ((ACT m) c1 v1))
             (* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1)))))))))))))))))))
(dk-peel!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(fact 'nvs-act-in-vec 'm 'c1 'v1)
(fact 'vnrm-real 'm 'v1) (fact 'vnrm-real 'm 'v2)
(fact 'vnrm-nonneg 'm 'v1) (fact 'vnrm-nonneg 'm 'v2)
(fact 'vnrm-real 'm '((ACT m) c1 v1))
(fact 'nvs-vnrm-homog 'm 'c1 'v1)
(fact 'rr-abs-closed 'c1)
(fact 'rr-mul-le-right '(abs c1) 'bd '((VNRM m) v1))
(have! '(AND (IN bd RR) (IN ((VNRM m) v2) RR)))
(have! '(AND (<= 0 bd) (<= 0 ((VNRM m) v2))))
(fact 'rr-leq-mul-nonneg 'bd '((VNRM m) v2))
(define r8f-1tsum '(+ (* bd ((VNRM m) v2)) (* bd ((VNRM m) v1))))
(have! (list '= '(* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1))))
                (list '+ 'bd r8f-1tsum))
       (lambda () (crs)))
(subst (list '= '(* bd (+ 1 (+ ((VNRM m) v2) ((VNRM m) v1))))
                (list '+ 'bd r8f-1tsum)))
(r8f-le-refl! '(* bd ((VNRM m) v1)))
(r8f-le-add! 0 '(* bd ((VNRM m) v2)) '(* bd ((VNRM m) v1)) '(* bd ((VNRM m) v1)))
(r8f-le-add! 0 'bd '(+ 0 (* bd ((VNRM m) v1))) r8f-1tsum)
(have! (list '= '(* bd ((VNRM m) v1)) '(+ 0 (+ 0 (* bd ((VNRM m) v1)))))
       (lambda () (crs)))
(r8f-eq-le! '(* bd ((VNRM m) v1)) '(+ 0 (+ 0 (* bd ((VNRM m) v1)))))
(r8f-le-trans! '(* bd ((VNRM m) v1)) '(+ 0 (+ 0 (* bd ((VNRM m) v1))))
               (list '+ 'bd r8f-1tsum))
(r8f-le-trans! '(* (abs c1) ((VNRM m) v1)) '(* bd ((VNRM m) v1))
               (list '+ 'bd r8f-1tsum))
(r8f-eq-le! '((VNRM m) ((ACT m) c1 v1)) '(* (abs c1) ((VNRM m) v1)))
(r8f-le-trans! '((VNRM m) ((ACT m) c1 v1)) '(* (abs c1) ((VNRM m) v1))
               (list '+ 'bd r8f-1tsum))
(ass)
(r8f-check! 'nvs-norm-one-term-bound)

;;; (x - z) = (x - y) + (y - z).  `crs' declines this identity on the CORNER
;;; TERMS themselves (three f-applications, 2026-09-19 probe); quantified over
;;; plain reals it goes through, and the instance is one citation.
(sp (make-wff
  '(FORALL x_ (IMPLIES (IN x_ RR)
     (FORALL y_ (IMPLIES (IN y_ RR)
     (FORALL z_ (IMPLIES (IN z_ RR)
       (= (- x_ z_) (+ (- x_ y_) (- y_ z_)))))))))))
(dk-peel!)
(crs)
(r8f-check! 'rr-diff-split-mid)

;;; =====================================================================
;;; 7.  dir-deriv-corner-split -- the notes' corner decomposition, with the
;;; two mean-value points EXHIBITED and their distance to a bounded.
;;;
;;;   F(t) - F(0) = t * (d_eta f(p1) + d_xi f(p2)),
;;;   d(a, p_i) <= |t| * (1 + ||eta|| + ||xi||)
;;;
;;; p1 = (a + t.xi) + (th*t).eta is the mean-value point of the eta-leg from
;;; the corner a + t.xi, p2 = a + (rh*t).xi that of the xi-leg from a.
;;; =====================================================================

(define (r8f-ex-for dir)
  (r8f-find (list 'the 'existence 'hypothesis 'for dir)
    (lambda (fm)
      (and ((r8f-cons-head? 'FORSOME) fm)
           (let ((body (caddr (caddr (caddr fm)))))
             (and (pair? body) (eq? (car body) 'IS-DIR-DIFF-AT)
                  (equal? (list-ref body 4) dir)))))))

;; land (IN (DIR-DERIV m f point dir) RR) through the existence hypothesis EX
(define (r8f-dd-real! ex point dir)
  (let* ((inst (dk-deepest (lambda () (inst+ ex point))))
         (sk (dk-landed-1 (lambda () (ai inst))))
         (kv (list-ref sk 5))
         (dd (list 'DIR-DERIV 'm 'f point dir)))
    (fact 'dir-deriv-value 'm 'f point dir kv)
    (fact 'dir-diff-value-in-rr 'm 'f point dir kv)
    (have! (list 'IN dd 'RR)
           (lambda () (subst (list '= dd kv)) (ass)))
    dd))

(sp (make-wff
  '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL a (IMPLIES (IN a (VEC m))
     (FORALL eta (IMPLIES (IN eta (VEC m))
     (FORALL xi (IMPLIES (IN xi (VEC m))
     (FORALL t_ (IMPLIES (IN t_ RR)
       (IMPLIES (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (FORSOME k_ (IS-DIR-DIFF-AT m f x_ eta k_))))
       (IMPLIES (FORALL x_ (IMPLIES (IN x_ (VEC m))
                   (FORSOME k_ (IS-DIR-DIFF-AT m f x_ xi k_))))
         (FORSOME p1 (FORSOME p2
           (AND (IN p1 (VEC m))
           (AND (IN p2 (VEC m))
           (AND (<= ((DIST (NVS-METRIC-SPACE m)) a p1)
                    (* (abs t_) (+ 1 (+ ((VNRM m) eta) ((VNRM m) xi)))))
           (AND (<= ((DIST (NVS-METRIC-SPACE m)) a p2)
                    (* (abs t_) (+ 1 (+ ((VNRM m) eta) ((VNRM m) xi)))))
                (= (- ((SEG-CURVE m f a ((VADD m) eta xi)) t_)
                      ((SEG-CURVE m f a ((VADD m) eta xi)) 0))
                   (* t_ (+ (DIR-DERIV m f p1 eta)
                            (DIR-DERIV m f p2 xi))))))))))))))))))))))))))
(dk-peel!)
(define r8f-exE (r8f-ex-for 'eta))
(define r8f-exX (r8f-ex-for 'xi))
(define r8f-w '((VADD m) eta xi))
(define r8f-FF (list 'SEG-CURVE 'm 'f 'a r8f-w))
(define r8f-b1 '((VADD m) a ((ACT m) t_ xi)))
(fact 'rr-zero-in) (fact 'rr-one-in)
(fact 'rr-abs-closed 't_) (fact 'rr-abs-nonneg 't_)
(fact 'rr-leq-reflexive '(abs t_))
(fact 'nvs-vadd-in-vec 'm 'eta 'xi)
(fact 'nvs-act-in-vec 'm 't_ 'xi)
(fact 'nvs-act-in-vec 'm 't_ 'eta)
(fact 'nvs-vadd-in-vec 'm 'a '((ACT m) t_ xi))
(fact 'vnrm-real 'm 'eta) (fact 'vnrm-real 'm 'xi)

;;; the two mean-value legs
(fact 'dir-deriv-increment-scaled 'm 'f 'a 'xi 't_)
(r8f-split-all!)
(define r8f-eq2
  (r8f-find "the xi leg"
    (lambda (fm) (and (pair? fm) (eq? (car fm) '=)
                      (equal? (cadr fm)
                              (list '- (list 'f r8f-b1) '(f a)))))))
(define r8f-P2 (list-ref (caddr (caddr r8f-eq2)) 3))
(define r8f-rh (cadr (cadr (caddr r8f-P2))))

(fact 'dir-deriv-increment-scaled 'm 'f r8f-b1 'eta 't_)
(r8f-split-all!)
(define r8f-eq1
  (r8f-find "the eta leg"
    (lambda (fm) (and (pair? fm) (eq? (car fm) '=)
                      (equal? (cadr fm)
                              (list '- (list 'f (list '(VADD m) r8f-b1 '((ACT m) t_ eta)))
                                       (list 'f r8f-b1)))))))
(define r8f-P1 (list-ref (caddr (caddr r8f-eq1)) 3))
(define r8f-th (cadr (cadr (caddr r8f-P1))))
(define r8f-ue (list '(ACT m) (list '* r8f-th 't_) 'eta))
(define r8f-ux (list '(ACT m) (list '* r8f-rh 't_) 'xi))
(define r8f-disp (list '(VADD m) '((ACT m) t_ xi) r8f-ue))

(r8f-real! (list '* r8f-th 't_))
(r8f-real! (list '* r8f-rh 't_))
(fact 'nvs-act-in-vec 'm (list '* r8f-th 't_) 'eta)
(fact 'nvs-act-in-vec 'm (list '* r8f-rh 't_) 'xi)
(fact 'nvs-vadd-in-vec 'm r8f-b1 '((ACT m) t_ eta))       ; the far corner
(fact 'nvs-vadd-in-vec 'm r8f-b1 r8f-ue)                 ; p1
(fact 'nvs-vadd-in-vec 'm 'a r8f-ux)                     ; p2
(fact 'nvs-vadd-in-vec 'm '((ACT m) t_ xi) r8f-ue)       ; the p1 displacement
(fact 'nvs-vadd-in-vec 'm 'a r8f-disp)
(fact 'rr-abs-unit-scale r8f-th 't_)
(fact 'rr-abs-unit-scale r8f-rh 't_)

;;; p1 = a (+) (t.xi (+) (th*t).eta)
(fact 'nvs-vadd-assoc 'm 'a '((ACT m) t_ xi) r8f-ue)
;;; the corner identity  (a + t.xi) + t.eta = a + t.(eta+xi)
(have! (list '= (list '(VADD m) r8f-b1 '((ACT m) t_ eta))
                (list '(VADD m) 'a (list '(ACT m) 't_ r8f-w)))
  (lambda ()
    (subst (dk-fact! 'nvs-vadd-assoc 'm 'a '((ACT m) t_ xi) '((ACT m) t_ eta)))
    (subst (dk-fact! 'nvs-vadd-comm 'm '((ACT m) t_ xi) '((ACT m) t_ eta)))
    (subst (dk-fact! 'nvs-act-distrib-vec-rr 'm 't_ 'eta 'xi))
    (fact 'nvs-vadd-in-vec 'm '((ACT m) t_ eta) '((ACT m) t_ xi))
    (fact 'nvs-vadd-in-vec 'm 'a '((VADD m) ((ACT m) t_ eta) ((ACT m) t_ xi)))
    (rfl)))

(ew r8f-P1)
(ew r8f-P2)
(r8f-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'IN) (ass))
       ((and (eq? (car g) '<=) (equal? (caddr (cadr g)) r8f-P1))
        (subst (list '= r8f-P1 (list '(VADD m) 'a r8f-disp)))
        (subst (dk-fact! 'nvs-dist-shift 'm 'a r8f-disp))
        (fact 'nvs-norm-two-term-bound 'm 'xi 'eta 't_ (list '* r8f-th 't_) '(abs t_))
        (ass))
       ((eq? (car g) '<=)
        (subst (dk-fact! 'nvs-dist-shift 'm 'a r8f-ux))
        (fact 'nvs-norm-one-term-bound 'm 'xi 'eta (list '* r8f-rh 't_) '(abs t_))
        (ass))
       (#t
        (let ((d1 (r8f-dd-real! r8f-exE r8f-P1 'eta))
              (d2 (r8f-dd-real! r8f-exX r8f-P2 'xi)))
          (fact 'fun-apply-type-c 'f '(VEC m) 'RR 'a)
          (fact 'fun-apply-type-c 'f '(VEC m) 'RR r8f-b1)
          (fact 'fun-apply-type-c 'f '(VEC m) 'RR (list '(VADD m) r8f-b1 '((ACT m) t_ eta)))
          (subst (dk-fact! 'seg-curve-apply 'm 'f 'a r8f-w 't_))
          (subst (dk-fact! 'seg-curve-apply 'm 'f 'a r8f-w 0))
          (subst (dk-fact! 'nvs-act-zero 'm r8f-w 'a))
          (subst (list '= (list '(VADD m) 'a (list '(ACT m) 't_ r8f-w))
                          (list '(VADD m) r8f-b1 '((ACT m) t_ eta))))
          (have! (list '= (list '* 't_ (list '+ d1 d2))
                          (list '+ (list '* 't_ d1) (list '* 't_ d2)))
                 (lambda () (crs)))
          (subst (list '= (list '* 't_ (list '+ d1 d2))
                          (list '+ (list '* 't_ d1) (list '* 't_ d2))))
          (subst (list '= (list '* 't_ d1) (cadr r8f-eq1)))
          (subst (list '= (list '* 't_ d2) (cadr r8f-eq2)))
          (fact 'rr-diff-split-mid
                (list 'f (list '(VADD m) r8f-b1 '((ACT m) t_ eta)))
                (list 'f r8f-b1) '(f a))
          (ass)))))))
(r8f-check! 'dir-deriv-corner-split)

;;; =====================================================================
;;; 8.  THE CARATHEODORY FACTOR.  There is no difference-quotient
;;; characterisation of the derivative in the tree (diff-at-local.scm's header
;;; says so), so the factor is built and totalised by an IF, exactly as
;;; `diff-at-local' totalises its own witness:
;;;
;;;     PSI(z) = IF z = 0 THEN dl+dm ELSE (F(z) - F(0)) * recip(z)
;;;
;;; Three facts about it are proved here -- it is a map RR -> RR, its value at 0,
;;; and the Caratheodory identity, which holds by construction at every real.
;;; What remains for `dir-deriv-additive' itself is the CONTINUITY of PSI at 0;
;;; see the closing note.
;;; =====================================================================

;;; (d*r)*(u-0) = d*(u*r) -- `crs' declines any term containing `recip', so the
;;; identity is proved with the reciprocal QUANTIFIED and instantiated after.
(sp (make-wff
  '(FORALL d_ (IMPLIES (IN d_ RR)
     (FORALL u_ (IMPLIES (IN u_ RR)
     (FORALL r_ (IMPLIES (IN r_ RR)
       (= (* (* d_ r_) (- u_ 0)) (* d_ (* u_ r_)))))))))))
(dk-peel!)
(crs)
(r8f-check! 'rr-factor-shift)

(define r8f-mw '((VADD m) eta xi))
(define r8f-mF (list 'SEG-CURVE 'm 'f 'a r8f-mw))
(define (r8f-ifq u)
  (list 'IF (list '= u 0) '(+ dl dm)
        (list '* (list '- (list r8f-mF u) (list r8f-mF 0)) (list 'recip u))))
(define r8f-psi (list 'VNB-LAMBDA 'z_ 'RR (r8f-ifq 'z_)))

(define (r8f-guards body)
  `(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL a (IMPLIES (IN a (VEC m))
     (FORALL eta (IMPLIES (IN eta (VEC m))
     (FORALL xi (IMPLIES (IN xi (VEC m))
     (FORALL dl (IMPLIES (IN dl RR)
     (FORALL dm (IMPLIES (IN dm RR) ,body)))))))))))))))

(define (r8f-quotient-setup!)
  (fact 'rr-zero-in)
  (fact 'nvs-vadd-in-vec 'm 'eta 'xi)
  (fact 'seg-curve-in-fun 'm 'f 'a r8f-mw)
  (fact 'fun-apply-type-c r8f-mF 'RR 'RR 0)
  (have! '(IN (+ dl dm) RR) (lambda () (in-rr))))

;;; (a) PSI is a map RR -> RR
(sp (make-wff (r8f-guards (list 'IN r8f-psi '(FUN RR RR)))))
(dk-peel!)
(r8f-quotient-setup!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let* ((zv (r8f-di-var!))
              (dd (list '- (list r8f-mF zv) (list r8f-mF 0))))
         (fact 'fun-apply-type-c r8f-mF 'RR 'RR zv)
         (fact 'rr-sub-in-rr (list r8f-mF zv) (list r8f-mF 0))
         (use-em (list '= zv 0)
           (lambda ()
             (for-each (lambda (l) (dk-focus! l)
                         (if (eq? (car (dk-goal)) '=) (ass)
                             (begin (subst (list '= (r8f-ifq zv) '(+ dl dm))) (ass))))
                       (dk-opened (lambda () (if-true (r8f-ifq zv))))))
           (lambda ()
             (for-each (lambda (l) (dk-focus! l)
                         (if (eq? (car (dk-goal)) 'NOT) (ass)
                             (begin
                               (subst (list '= (r8f-ifq zv) (list '* dd (list 'recip zv))))
                               (have! (list 'AND (list 'IN zv 'RR)
                                            (list 'NOT (list '= zv 0))))
                               (fact 'rr-recip-closed zv)
                               (have! (list 'AND (list 'IN dd 'RR)
                                            (list 'IN (list 'recip zv) 'RR)))
                               (fact 'rr-mul-closed dd (list 'recip zv))
                               (ass))))
                       (dk-opened (lambda () (if-false (r8f-ifq zv))))))))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(r8f-check! 'dir-quotient-in-fun)

;;; (b) PSI(0) = dl + dm
(sp (make-wff (r8f-guards (list '= (list r8f-psi 0) '(+ dl dm)))))
(dk-peel!)
(r8f-quotient-setup!)
(lam-b)
(for-each (lambda (l) (dk-focus! l)
            (if (equal? (dk-goal) '(= 0 0)) (rfl)
                (begin (subst (list '= (r8f-ifq 0) '(+ dl dm))) (rfl))))
          (dk-opened (lambda () (if-true (r8f-ifq 0)))))
(r8f-check! 'dir-quotient-at-zero)

;;; (c) the Caratheodory identity, at every real
(sp (make-wff (r8f-guards
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
    (list '= (list '- (list r8f-mF 'x_) (list r8f-mF 0))
             (list '* (list r8f-psi 'x_) '(- x_ 0))))))))
(dk-peel!)
(r8f-quotient-setup!)
;; `dk-peel!' has already peeled the inner universal and landed its guard: the
;; eigenvariable is read off the GOAL, never re-introduced.
(let* ((zv (cadr (cadr (cadr (dk-goal)))))
       (dd (list '- (list r8f-mF zv) (list r8f-mF 0))))
  (fact 'fun-apply-type-c r8f-mF 'RR 'RR zv)
  (fact 'rr-sub-in-rr (list r8f-mF zv) (list r8f-mF 0))
  (lam-b)
  (use-em (list '= zv 0)
    (lambda ()
      (for-each (lambda (l) (dk-focus! l)
                  (if (equal? (dk-goal) (list '= zv 0)) (ass)
                      (begin (subst (list '= (r8f-ifq zv) '(+ dl dm)))
                             (subst (list '= zv 0))
                             (crs))))
                (dk-opened (lambda () (if-true (r8f-ifq zv))))))
    (lambda ()
      (for-each (lambda (l) (dk-focus! l)
                  (if (eq? (car (dk-goal)) 'NOT) (ass)
                      (begin
                        (subst (list '= (r8f-ifq zv) (list '* dd (list 'recip zv))))
                        (have! (list 'AND (list 'IN zv 'RR) (list 'NOT (list '= zv 0))))
                        (fact 'rr-recip-closed zv)
                        (fact 'rr-recip-inverse zv)
                        (fact 'rr-factor-shift dd zv (list 'recip zv))
                        (subst (list '= (list '* (list '* dd (list 'recip zv))
                                                 (list '- zv 0))
                                        (list '* dd (list '* zv (list 'recip zv)))))
                        (subst (list '= (list '* zv (list 'recip zv)) 1))
                        (crs))))
                (dk-opened (lambda () (if-false (r8f-ifq zv))))))))
(r8f-check! 'dir-quotient-identity)

;;; =====================================================================
;;; 9.  dir-quotient-continuous -- PSI is continuous at 0.  This is the notes'
;;; eps/delta argument, and the only part of Lemma 2.26 that is not algebra.
;;; =====================================================================

;;; (u*s)*r = s*(u*r) -- `crs' declines any term containing `recip', so the two
;;; cancellations below go through this quantified identity.
(sp (make-wff
  '(FORALL s_ (IMPLIES (IN s_ RR)
     (FORALL u_ (IMPLIES (IN u_ RR)
     (FORALL r_ (IMPLIES (IN r_ RR)
       (= (* (* u_ s_) r_) (* s_ (* u_ r_)))))))))))
(dk-peel!)
(crs)
(r8f-check! 'rr-mul-rotate)

(define r8f-mC '(+ 1 (+ ((VNRM m) eta) ((VNRM m) xi))))
(define (r8f-lam dir) (list 'VNB-LAMBDA 'x_ '(VEC m) (list 'DIR-DERIV 'm 'f 'x_ dir)))
(define (r8f-ct dir) (list 'IS-CONTINUOUS-AT '(NVS-METRIC-SPACE m) 'RR-MS (r8f-lam dir) 'a))
(define (r8f-ex dir)
  (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (VEC m))
        (list 'FORSOME 'k_ (list 'IS-DIR-DIFF-AT 'm 'f 'x_ dir 'k_)))))

;; the inner universal of an unfolded IS-CONTINUOUS-AT, at the half HF
(define (r8f-delta-for! ctform hf)
  (let* ((parts (dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'is-continuous-at ctform))))))
         (univ (r8f-find "the eps clause of a continuity hypothesis"
                 (lambda (fm) (and ((r8f-cons-head? 'FORSOME) fm)
                                   (dk-contains? fm 'POS-RR)))))
         (inst (dk-deepest (lambda () (inst+ univ hf))))
         (sk   (dk-landed-1 (lambda () (ai inst)))))
    (dk-split-all! (list sk))
    (let* ((dv (cadr (r8f-find "the delta"
                       (lambda (fm) (and (pair? fm) (eq? (car fm) 'POS-RR)
                                         (not (equal? (cadr fm) hf))))))))
      (fact 'rr-pos-rr-in-rr dv)
      (fact 'rr-lt-of-pos-rr dv)
      (list dv (r8f-find "the delta clause"
                 (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                   (dk-contains? fm dv)
                                   (dk-contains? fm 'DIST))))))))

(sp (make-wff
  `(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL f (IMPLIES (IN f (FUN (VEC m) RR))
     (FORALL a (IMPLIES (IN a (VEC m))
     (FORALL eta (IMPLIES (IN eta (VEC m))
     (FORALL xi (IMPLIES (IN xi (VEC m))
     (FORALL dl (IMPLIES (IS-DIR-DIFF-AT m f a eta dl)
     (FORALL dm (IMPLIES (IS-DIR-DIFF-AT m f a xi dm)
       (IMPLIES ,(r8f-ex 'eta)
       (IMPLIES ,(r8f-ex 'xi)
       (IMPLIES ,(r8f-ct 'eta)
       (IMPLIES ,(r8f-ct 'xi)
         (IS-CONTINUOUS-AT RR-MS RR-MS ,r8f-psi 0)))))))))))))))))))))
(dk-peel!)
(define r8f-cEX (r8f-ex-for 'eta))      ; found in the CONTEXT, never rebuilt
(define r8f-cEXX (r8f-ex-for 'xi))
(fact 'rr-zero-in) (fact 'rr-one-in)
(fact 'rr-is-metric-space)
(fact 'dir-diff-value-in-rr 'm 'f 'a 'eta 'dl)
(fact 'dir-diff-value-in-rr 'm 'f 'a 'xi 'dm)
(fact 'dir-deriv-value 'm 'f 'a 'eta 'dl)
(fact 'dir-deriv-value 'm 'f 'a 'xi 'dm)
;; `rr-ms-dist' is GUARDED on both arguments, and the base point's value enters
;; it as the DIR-DERIV term, not as dl: type that term, not just its value.
(have! '(IN (DIR-DERIV m f a eta) RR)
       (lambda () (subst '(= (DIR-DERIV m f a eta) dl)) (ass)))
(have! '(IN (DIR-DERIV m f a xi) RR)
       (lambda () (subst '(= (DIR-DERIV m f a xi) dm)) (ass)))
(fact 'nvs-vadd-in-vec 'm 'eta 'xi)
(fact 'seg-curve-in-fun 'm 'f 'a r8f-mw)
(fact 'fun-apply-type-c r8f-mF 'RR 'RR 0)
(have! '(IN (+ dl dm) RR) (lambda () (in-rr)))
(fact 'vnrm-real 'm 'eta) (fact 'vnrm-real 'm 'xi)
(fact 'vnrm-nonneg 'm 'eta) (fact 'vnrm-nonneg 'm 'xi)
(r8f-real! r8f-mC)
(have! (list '< 0 r8f-mC)
       (lambda () (r8f-ineq '(<= 0 ((VNRM m) eta)) '(<= 0 ((VNRM m) xi)))))
(have! (list 'NOT (list '= r8f-mC 0))
       (lambda ()
         (mac-h '< (list '< 0 r8f-mC))
         (dk-split! (list 'AND (list '<= 0 r8f-mC)
                          (list 'NOT (list '= 0 r8f-mC))))
         (fact 'neq-sym 0 r8f-mC)
         (ass)))
(have! (list 'AND (list 'IN r8f-mC 'RR) (list 'NOT (list '= r8f-mC 0))))
(fact 'rr-recip-closed r8f-mC)
(fact 'rr-recip-inverse r8f-mC)                       ; C * recip C = 1
(fact 'rr-recip-pos r8f-mC)                           ; 0 < recip C
(fact 'rr-lt-implies-le 0 r8f-mC)
(define r8f-rc (list 'recip r8f-mC))
(have! (list 'AND (list 'IN r8f-mC 'RR) (list 'IN r8f-rc 'RR)))
(fact 'rr-mul-comm r8f-mC r8f-rc)                     ; recip C * C = C * recip C
(fact 'dir-quotient-in-fun 'm 'f 'a 'eta 'xi 'dl 'dm)
(fact 'dir-quotient-at-zero 'm 'f 'a 'eta 'xi 'dl 'dm)
(fact 'fun-apply-type-c r8f-psi 'RR 'RR 0)

(mac 'is-continuous-at)
(r8f-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
       ((eq? (car g) 'FORALL)
        ;; ---- the eps lane ------------------------------------------------
        ;; the eps clause is guarded by POS-RR, not by IN, so one `di' peels the
        ;; universal and lands NOTHING: peel by GOAL HEAD down to the FORSOME.
        (let* ((land (dk-landed (lambda () (r8f-to-head! 'FORSOME))))
               (pos (or (find-first (lambda (fm) (and (pair? fm) (eq? (car fm) 'POS-RR)))
                                    land)
                        (error "rake-dir-deriv-additive: no POS-RR landed")))
               (eps (cadr pos))
               (hf  (dk-halve! eps)))
          (r8f-split-all!)
          (fact 'rr-pos-rr-in-rr eps)
          (fact 'rr-lt-of-pos-rr eps)
          (fact 'rr-lt-implies-le 0 eps)
          (fact 'nvs-metric-is-ms 'm)
          (have! '(IN a (PTS (NVS-METRIC-SPACE m)))
                 (lambda () (mac 'nvs-ms-pts) (ass)))
          (let* ((de (r8f-delta-for! (r8f-ct 'eta) hf))
                 (dx (r8f-delta-for! (r8f-ct 'xi) hf))
                 (d1 (car de)) (d2 (car dx))
                 (cl1 (cadr de)) (cl2 (cadr dx)))
            (fact 'rr-min-pos d1 d2)
            (r8f-split-all!)
            (let* ((mn (cadr (r8f-find "the minimum"
                               (lambda (fm) (and (pair? fm) (eq? (car fm) '<=)
                                                 (equal? (caddr fm) d1)
                                                 (not (equal? (cadr fm) d1)))))))
                   (dlt (list '* mn r8f-rc)))
              (have! (list 'AND (list 'IN mn 'RR) (list 'IN r8f-rc 'RR)))
              (fact 'rr-mul-closed mn r8f-rc)
              (fact 'rr-mul-pos mn r8f-rc)              ; 0 < delta
              (fact 'rr-pos-rr-of-lt dlt)               ; POS-RR delta
              ;; delta * C = mn
              (have! (list 'AND (list 'IN mn 'RR)
                           (list 'AND (list 'IN r8f-rc 'RR) (list 'IN r8f-mC 'RR))))
              (fact 'rr-mul-assoc mn r8f-rc r8f-mC)
              (have! (list '= (list '* dlt r8f-mC) mn)
                (lambda ()
                  (subst (list '= (list '* dlt r8f-mC)
                                  (list '* mn (list '* r8f-rc r8f-mC))))
                  (subst (list '= (list '* r8f-rc r8f-mC) (list '* r8f-mC r8f-rc)))
                  (subst (list '= (list '* r8f-mC r8f-rc) 1))
                  (crs)))
              (ew dlt)
              (r8f-and!
               (lambda ()
                 (if (not (eq? (car (dk-goal)) 'FORALL))
                     (ass)
                     ;; ---- the point lane --------------------------------
                     (let* ((land (dk-landed (lambda () (r8f-to-head! '<=))))
                            (mem (or (find-first (lambda (fm)
                                                   (and (pair? fm) (eq? (car fm) 'IN))) land)
                                     (error "r8f: no point membership landed")))
                            (bv (cadr mem))
                            (dhyp (or (find-first (lambda (fm)
                                                    (and (pair? fm) (eq? (car fm) '<=))) land)
                                      (error "r8f: no distance hypothesis landed"))))
                       (slot-h 'PTS mem)                 ; bv in RR
                       (fact 'fun-apply-type-c r8f-psi 'RR 'RR bv)
                       (fact 'rr-ms-dist 0 bv)
                       (fact 'rr-abs-neg bv)
                       (fact 'rr-abs-closed bv)
                       (have! (list '= (list '- bv) (list '- 0 bv)) (lambda () (crs)))
                       (have! (list '<= (list 'abs bv) dlt)
                         (lambda ()
                           (subst (list '= (list 'abs bv) (list 'abs (list '- bv))))
                           (subst (list '= (list '- bv) (list '- 0 bv)))
                           (subst (list '= (list 'abs (list '- 0 bv))
                                           (list '(DIST RR-MS) 0 bv)))
                           (ass)))
                       ;; the goal, with the RR-MS distance written as an abs
                       (mac 'rr-ms-dist)
                       (use-em (list '= bv 0)
                         ;; ---- b = 0 -----------------------------------
                         (lambda ()
                           (subst (list '= bv 0))
                           (have! (list '= (list '- (list r8f-psi 0) (list r8f-psi 0)) 0)
                                  (lambda () (crs)))
                           (subst (list '= (list '- (list r8f-psi 0) (list r8f-psi 0)) 0))
                           (fact 'rr-leq-reflexive 0)
                           (fact 'rr-abs-of-nonneg 0)
                           (subst '(= (abs 0) 0))
                           (ass))
                         ;; ---- b /= 0 ----------------------------------
                         (lambda ()
                           (fact 'dir-deriv-corner-split 'm 'f 'a 'eta 'xi bv)
                           (r8f-split-all!)
                           (let* ((ceq (r8f-find "the corner equation"
                                         (lambda (fm)
                                           (and (pair? fm) (eq? (car fm) '=)
                                                (equal? (cadr fm)
                                                        (list '- (list r8f-mF bv)
                                                                 (list r8f-mF 0)))))))
                                  (sum (caddr (caddr ceq)))      ; D1 + D2
                                  (dd1 (cadr sum)) (dd2 (caddr sum))
                                  (p1 (list-ref dd1 3)) (p2 (list-ref dd2 3)))
                             (r8f-dd-real! r8f-cEX p1 'eta)
                             (r8f-dd-real! r8f-cEXX p2 'xi)
                             (r8f-real! sum)
                             ;; PSI(b) = D1 + D2
                             (have! (list 'AND (list 'IN bv 'RR) (list 'NOT (list '= bv 0))))
                             (fact 'rr-recip-closed bv)
                             (fact 'rr-recip-inverse bv)
                             (fact 'rr-mul-rotate sum bv (list 'recip bv))
                             (have! (list '= (list r8f-psi bv) sum)
                               (lambda ()
                                 (lam-b)
                                 (for-each
                                  (lambda (l) (dk-focus! l)
                                    (if (eq? (car (dk-goal)) 'NOT) (ass)
                                        (begin
                                          (subst (list '= (r8f-ifq bv)
                                                       (list '* (list '- (list r8f-mF bv)
                                                                        (list r8f-mF 0))
                                                             (list 'recip bv))))
                                          (subst ceq)
                                          (subst (list '= (list '* (list '* bv sum)
                                                                   (list 'recip bv))
                                                          (list '* sum (list '* bv
                                                                          (list 'recip bv)))))
                                          (subst (list '= (list '* bv (list 'recip bv)) 1))
                                          (crs))))
                                  (dk-opened (lambda () (if-false (r8f-ifq bv)))))))
                             ;; the two distance bounds reach d1 and d2
                             (fact 'rr-mul-le-right (list 'abs bv) dlt r8f-mC)
                             (r8f-eq-le! (list '* dlt r8f-mC) mn)
                             (r8f-le-trans! (list '* (list 'abs bv) r8f-mC)
                                            (list '* dlt r8f-mC) mn)
                             (for-each
                              (lambda (pr)
                                (let ((pt (car pr)) (dv (cadr pr)) (cl (caddr pr))
                                      (dr (cadddr pr)) (base (car (cddddr pr))))
                                  ;; the DISTANCE is not arithmetic: `in-rr' cannot type
                                  ;; it, and every <= chaining step wants the typing.
                                  (have! (list 'IN pt '(PTS (NVS-METRIC-SPACE m)))
                                         (lambda () (mac 'nvs-ms-pts) (ass)))
                                  (fact 'metric-dist-real '(NVS-METRIC-SPACE m) 'a pt)
                                  (r8f-le-trans! (list '* (list 'abs bv) r8f-mC) mn dv)
                                  (r8f-le-trans! (list '(DIST (NVS-METRIC-SPACE m)) 'a pt)
                                                 (list '* (list 'abs bv) r8f-mC) dv)
                                  (let* ((u1 (dk-deepest (lambda () (inst+ cl pt))))
                                         (u2 (dk-landed-1 (lambda () (lam-b-h u1))))
                                         (dda (list 'DIR-DERIV 'm 'f 'a dr))
                                         (ddp (list 'DIR-DERIV 'm 'f pt dr)))
                                    (fact 'rr-ms-dist dda ddp)
                                    (have! (list '<= (list 'abs (list '- base ddp)) hf)
                                      (lambda ()
                                        (subst (list '= base dda))
                                        (subst (list '= (list 'abs (list '- dda ddp))
                                                        (list '(DIST RR-MS) dda ddp)))
                                        (ass))))))
                              (list (list p1 d1 cl1 'eta 'dl)
                                    (list p2 d2 cl2 'xi 'dm)))
                             ;; |PSI(0) - PSI(b)| = |(dl+dm) - (D1+D2)| <= eps
                             (subst (list '= (list r8f-psi 0) '(+ dl dm)))
                             (subst (list '= (list r8f-psi bv) sum))
                             (have! (list 'AND
                                          (list 'AND
                                                (list '<= (list 'abs (list '- 'dl dd1)) hf)
                                                (list '<= (list 'abs (list '- 'dm dd2)) hf))
                                          (list '= (list '+ hf hf) eps)))
                             (fact 'rr-abs-sum-bound 'dl 'dm dd1 dd2 hf eps)
                             (ass))))))))))))
       (#t (ass))))))
(r8f-check! 'dir-quotient-continuous)

;;; =====================================================================
;;; THE FINDING OF THIS ASSIGNMENT
;;; =====================================================================
;;;
;;; `ineq' DROPS, silently, every premise that is not linear in RR, and a product
;;; of two non-constant terms -- |c| * ||v||, |t| * C -- is exactly that; the call
;;; then declines and the message blames the GOAL.  The whole estimate in Lemma
;;; 2.26 is products of that shape, so sections 6, 7 and 9 chain by citation
;;; instead: `rr-mul-le-right' for monotonicity, `rr-leq-transitive' /
;;; `rr-le-add' for the chaining, and `crs' on a QUANTIFIED companion wherever
;;; the term contains `recip' (crs declines those outright).  The three helpers
;;; r8f-le-trans! / r8f-le-add! / r8f-eq-le! above -- land the typings, cite the
;;; law -- are the shape that belongs in driver-kit.scm as a `dk-le-chain!'.
;;; `r8f-eq-le!' has to pick its rewrite direction by CONTAINMENT: `subst'
;;; rewrites EVERY occurrence, so `x = 0 + (0 + x)' loops if used forwards.
;;;
;;; =====================================================================
;;; 10.  LEMMA 2.26 -- dir-deriv-additive.  Statement copied LITERALLY from
;;; theorem-library/directional-derivative.scm:650-668 (the `add-to-pss' this
;;; retires), `conjuncts->and' included.
;;; =====================================================================

(sp (make-wff
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
       (IS-DIR-DIFF-AT m f a ((VADD m) eta xi) (+ dl dm))))))))))))
(dk-peel!)
(r8f-split-all!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(have! '(< 0 1) (lambda () (arith)))
(fact 'dir-diff-value-in-rr 'm 'f 'a 'eta 'dl)
(fact 'dir-diff-value-in-rr 'm 'f 'a 'xi 'dm)
(fact 'nvs-vadd-in-vec 'm 'eta 'xi)
(fact 'seg-curve-in-fun 'm 'f 'a r8f-mw)
(have! '(IN (+ dl dm) RR) (lambda () (in-rr)))
(fact 'dir-quotient-in-fun 'm 'f 'a 'eta 'xi 'dl 'dm)
(fact 'dir-quotient-at-zero 'm 'f 'a 'eta 'xi 'dl 'dm)
(fact 'dir-quotient-continuous 'm 'f 'a 'eta 'xi 'dl 'dm)
(define r8f-gid (dk-fact! 'dir-quotient-identity 'm 'f 'a 'eta 'xi 'dl 'dm))
;;; diff-at-local asks for the identity only on a ball; ours holds everywhere.
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
             (list 'IMPLIES (list '<= (list 'abs '(- x_ 0)) 1)
                   (list '= (list '- (list r8f-mF 'x_) (list r8f-mF 0))
                            (list '* (list r8f-psi 'x_) '(- x_ 0))))))
  (lambda ()
    (let* ((land (dk-landed (lambda () (r8f-to-head! '=))))
           (mem (or (find-first (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN))) land)
                    (error "rake-dir-deriv-additive: no ball membership landed")))
           (xv (cadr mem)))
      (dk-deepest (lambda () (inst+ r8f-gid xv)))
      (ass))))
(mac 'IS-DIR-DIFF-AT)
(fact 'diff-at-local r8f-mF r8f-psi 0 '(+ dl dm) 1)
(ass)
(r8f-check! 'dir-deriv-additive)
(alias! 'dir-deriv-additive "the directional derivative is additive in the direction")

;;; ---- SPLICE END 2026-09-19 -----------------------------------------

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
;; LUTINS instantiation (2026-09-18): `dir-deriv-additive' is cited below AT
;; the two products r*dl and s*dm, so the two derivative values have to be
;; typed first.  Each is the value of an IS-DIR-DIFF-AT hypothesis, two
;; unfolds away (IS-DIR-DIFF-AT is IS-DIFF-AT of the segment curve).
(dd-dirval-real! 'm 'f 'a 'eta 'dl)
(dd-dirval-real! 'm 'f 'a 'xi 'dm)
(have! '(IN (* r dl) RR) (lambda () (in-rr)))
(have! '(IN (* s dm) RR) (lambda () (in-rr)))
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
