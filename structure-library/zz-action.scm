;;; zz-action.scm -- ZZ-ACT: the integer action on an abelian group.
;;;
;;; The NN-action  n.a  (MPOW under the additive monoid, monoid-power.scm) makes
;;; the underlying commutative monoid of an abelian group an NN-semimodule.
;;; EXTENDING it to a ZZ-action -- making the abelian group a ZZ-module -- is a
;;; THEOREM, not automatic: it uses the group INVERSE to define negative scalars
;;; and then re-proves the module axioms across sign boundaries.  This file
;;; carries that step.
;;;
;;;   ZZ-ACT(g, k, a) = k . a       (k in ZZ, a in A(g))
;;;
;;; defined by two conditional equations splitting on the sign of k:
;;;   k in NN        :  ZZ-ACT(g, k, a)     = MPOW(g-as-monoid, a, k)
;;;   k in NN, k>0   :  ZZ-ACT(g, -k, a)    = INV(g)( MPOW(g-as-monoid, a, k) )
;;; where g-as-monoid = (ABELIAN-GROUP-AS-MONOID g).  The inverse is exactly the
;;; ingredient unavailable at the monoid / NN-semimodule layer.
;;;
;;; The ZZ-module axioms (zz-act-one, zz-act-add, zz-act-distrib, zz-act-assoc,
;;; zz-act-zero) then hold.  zz-act-add is the keystone: its proof is a sign-case
;;; analysis that reduces the mixed-sign cases to the NN law mpow-add together
;;; with inverse/cancellation -- the work the slogan "every abelian group is a
;;; ZZ-module" silently elides.  Asserted with `informal' warrants in the
;;; library-build phase: each warrant string is a paper-proof SKETCH, not a
;;; machine-checked VNB proof (which would rate the stronger `proof' tier).
;;;
;;; Dependencies: abelian-group.scm (IS-ABELIAN-GROUP, MUL, E, INV),
;;; monoid-power.scm (MPOW, mpow-add), views.scm (ABELIAN-GROUP-AS-MONOID),
;;; number-systems.scm (NN, ZZ, +, *, unary -).

;;; ---- Defining equations (split on sign of the integer scalar) -------------
(theory-add-definition! *current-theory* 'ZZ-ACT
  (list
    ;; Non-negative scalar: reuse the NN-action MPOW on the additive monoid.
    (cons 'zz-act-nonneg
      '(FORALL g
         (IMPLIES (IS-ABELIAN-GROUP g)
           (FORALL k (IMPLIES (IN k NN)
             (FORALL a (IMPLIES (IN a (CARR g))
               (= (ZZ-ACT g k a)
                  (MPOW (ABELIAN-GROUP-AS-MONOID g) a k)))))))))
    ;; Negative scalar: invert the corresponding positive power.
    (cons 'zz-act-neg
      '(FORALL g
         (IMPLIES (IS-ABELIAN-GROUP g)
           (FORALL k (IMPLIES (IN k NN)
             (FORALL a (IMPLIES (IN a (CARR g))
               (= (ZZ-ACT g (- k) a)
                  ((INV g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a k))))))))))))

;;; ---- Endpoints ------------------------------------------------------------
;;; 0 . a = E(g).
(theory-add-axiom! *current-theory* 'zz-act-zero
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL a (IMPLIES (IN a (CARR g))
         (= (ZZ-ACT g 0 a) (ID g)))))))
(warrant! 'zz-act-zero 'informal
  "0 in NN so zz-act-nonneg gives MPOW(.,a,0)=E(g) by mpow-zero and the view E-correspondence.")

;;; 1 . a = a.
(theory-add-axiom! *current-theory* 'zz-act-one
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL a (IMPLIES (IN a (CARR g))
         (= (ZZ-ACT g 1 a) a))))))
(warrant! 'zz-act-one 'informal
  "1 in NN so zz-act-nonneg gives MPOW(.,a,1)=a by mpow-one.")

;;; ---- Type ----------------------------------------------------------------
;;; k . a stays in the carrier, for every integer k.
(theory-add-axiom! *current-theory* 'zz-act-type
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL k (IMPLIES (IN k ZZ)
         (FORALL a (IMPLIES (IN a (CARR g))
           (IN (ZZ-ACT g k a) (CARR g)))))))))
(warrant! 'zz-act-type 'informal
  "Sign-case on k: nonneg branch is mpow-type (via the AG-as-MONOID view); neg branch closes under INV (group inverse stays in carrier).")

;;; ---- Sign law:  (-k) . a = -(k . a) --------------------------------------
;;; Holds for ALL integers k (the defining zz-act-neg is only the k in NN case).
(theory-add-axiom! *current-theory* 'zz-act-neg-sign
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL k (IMPLIES (IN k ZZ)
         (FORALL a (IMPLIES (IN a (CARR g))
           (= (ZZ-ACT g (- k) a) ((INV g) (ZZ-ACT g k a))))))))))
(warrant! 'zz-act-neg-sign 'informal
  "Two sub-cases (k>=0, k<0); the negative case uses double-inverse INV(INV x)=x.  Extends zz-act-neg from NN to all of ZZ.")

;;; ---- Keystone module law:  (j+k) . a = j.a + k.a -------------------------
;;; THE theorem that makes the extension a ZZ-module.  Proof is the sign-case
;;; analysis that reduces every mixed-sign combination to mpow-add plus
;;; inverse/cancellation in the group.
(theory-add-axiom! *current-theory* 'zz-act-add
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL j (IMPLIES (IN j ZZ)
         (FORALL k (IMPLIES (IN k ZZ)
           (FORALL a (IMPLIES (IN a (CARR g))
             (= (ZZ-ACT g (+ j k) a)
                ((MUL g) (ZZ-ACT g j a) (ZZ-ACT g k a))))))))))))
(warrant! 'zz-act-add 'informal
  "Keystone. Both nonneg: mpow-add directly. Mixed sign j>=0,k<0 (and symmetric): reduce via cancellation using INV against the NN identity mpow-add(min)+mpow-add(diff). Both negative: invert the all-positive case using AG commutativity. This is the content elided by 'rings are ZZ-modules'.")

;;; ---- Module distributivity:  k . (a + b) = k.a + k.b ---------------------
;;; Needs the group to be ABELIAN (commutativity of MUL) to interleave factors.
(theory-add-axiom! *current-theory* 'zz-act-distrib
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL k (IMPLIES (IN k ZZ)
         (FORALL a (IMPLIES (IN a (CARR g))
           (FORALL b (IMPLIES (IN b (CARR g))
             (= (ZZ-ACT g k ((MUL g) a b))
                ((MUL g) (ZZ-ACT g k a) (ZZ-ACT g k b))))))))))))
(warrant! 'zz-act-distrib 'informal
  "Nonneg case is mpow-mult on the (commutative) AG monoid; neg case applies INV to it using INV(MUL a b)=MUL(INV a)(INV b) in an abelian group.  Commutativity is essential.")

;;; ---- Mixed associativity:  (j*k) . a = j . (k . a) -----------------------
(theory-add-axiom! *current-theory* 'zz-act-assoc
  '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL j (IMPLIES (IN j ZZ)
         (FORALL k (IMPLIES (IN k ZZ)
           (FORALL a (IMPLIES (IN a (CARR g))
             (= (ZZ-ACT g (* j k) a)
                (ZZ-ACT g j (ZZ-ACT g k a))))))))))))
(warrant! 'zz-act-assoc 'informal
  "Sign-case on j and k; each reduces to iterating zz-act-add (k.a added j times) with sign bookkeeping handled by zz-act-neg-sign.")
