;;; poly-zero.scm -- the ZERO of a monoid algebra, pointwise, and the
;;; EXTENSIONALITY BRIDGE for polynomials.  Nothing here is asserted; every
;;; statement is `proven modulo 0'.
;;;
;;; WHAT THIS FILE CLOSES.  theorem-library/poly-degree-laws.scm proves
;;; `leadcoef-nonzero' from a POINTWISE hypothesis -- "p has some nonzero
;;; coefficient" -- where the mathematician writes "p /= 0".  Its own header
;;; recorded the gap between the two and stopped there:
;;;
;;;     the equivalence is FUNCTION EXTENSIONALITY composed with the pointwise
;;;     value of MONALG-ZERO, and neither is in the tree in citable form.
;;;
;;; Half of that was simply wrong.  `fun-domain-extensionality' (theory.scm) IS
;;; in the tree and is PRIMITIVE:
;;;
;;;     f in FUN(A) => g in FUN(A) => (forall x in A. f(x) = g(x)) => f = g
;;;
;;; -- full set-theoretic extensionality, no finiteness, no sethood side
;;; condition beyond membership in FUN(A).  The other half was right: the
;;; pointwise value of MONALG-ZERO did not exist.  It is `monalg-zero-apply'
;;; below, and it is one `lam-b' -- the exact twin of `monalg-add-apply'
;;; (theorem-library/monalg-laws.scm), which is the model this file follows
;;; throughout.
;;;
;;; ONE new statement of bridge shape, and only one: `poly-zero-iff'.  The
;;; standing rule is that per-operator congruence / replacement /
;;; "extensionality-of-OP" lemmas are NOT to be added -- chain through
;;; `fun-domain-extensionality' at the point of use instead.  This file cites it
;;; exactly once, inside the bridge's backward direction, and every other
;;; statement here is either a definitional projection (what the zero of the
;;; constructed structure IS, pointwise) or a typing.
;;;
;;; THE FIVE BRICKS, in dependency order:
;;;
;;;   monalg-zero-apply   (MONALG-ZERO(A,M))(x) == ZERO(A) for x in CARR(M).
;;;                       One `lam-b'.  `==', not `=': `rfl' carries a
;;;                       definedness side-condition and ZERO(A) is not
;;;                       syntactically defined, so the `=' form would owe a
;;;                       witness it does not need here.  monalg-add-apply's
;;;                       reasoning, verbatim.
;;;   monalg-zero-fun     MONALG-ZERO(A,M) in FUN(CARR M, CARR A).  `lam-t',
;;;                       whose two leaves are the constant typing and the
;;;                       sethood of the domain.  GUARDED ON THE TWO FACTS IT
;;;                       USES -- (IN (CARR m) SET) and (IN (ZERO a) (CARR a)) --
;;;                       rather than on IS-MONOID/IS-RING, for supp-in-set's
;;;                       reason: the polynomial case knows its carrier
;;;                       concretely (CARR(NN-ADD-MONOID) = NN, whose sethood is
;;;                       primitive) and should not have to route through
;;;                       IS-MONOID(NN-ADD-MONOID) to say so.
;;;   poly-zero-unfold    ZERO(POLY A) == MONALG-ZERO(A, NN-ADD-MONOID).
;;;                       poly-carrier's proof one slot over: POLY unfolds to
;;;                       MONALG, MONALG to the RING 6-tuple, ZERO projects
;;;                       slot 5.
;;;   poly-zero-apply     (ZERO(POLY A))(k) = ZERO(A) for k in NN.  Here the
;;;                       equality IS strict, and that is the point: the bridge
;;;                       must talk about `=' because `leadcoef-nonzero's
;;;                       hypothesis is a NEGATED `='.  `ring-zero-in' puts
;;;                       (ZERO a) in the carrier, which is what
;;;                       `asm-establishes-defined?' (primitive-inferences.scm)
;;;                       reads to let `rfl' close (ZERO a) = (ZERO a).  This is
;;;                       the only place IS-RING is needed, and it is needed for
;;;                       definedness alone.
;;;   poly-zero-fun       ZERO(POLY A) in FUN(NN, CARR A).
;;;
;;; and then the bridge:
;;;
;;;   poly-zero-iff       p in CARR(POLY A) =>
;;;                         ( p = ZERO(POLY A)  <=>  forall k in NN. p(k) = ZERO(A) )
;;;
;;; =>  is `subst' of the equation followed by poly-zero-apply.  Note that the
;;;     substitution rewrites p in OPERATOR position -- CLAUDE.md's warning that
;;;     `subst' cannot do that is about a COMPOUND left-hand side; for a bare
;;;     SYMBOL `replace-term' delegates to `subst-free', whose general-compound
;;;     branch substitutes a symbol head that is not a registered constant
;;;     (expressions.scm).  So (p_ k_) does become ((ZERO (POLY a_)) k_).
;;; <=  is `fun-domain-extensionality' at A := NN, after typing both sides into
;;;     FUN(NN).  Both typings come off FUN(NN, CARR A) by `fun-codomain-iff',
;;;     applied with `mac-h' and split -- NOT by `prop', which declines with 16
;;;     distinct atoms against a cap of 12 (*prop-atom-cap*) once the citation
;;;     chains are in the context.
;;;
;;; WHAT IT BUYS, in poly-degree-laws.scm: `leadcoef-nonzero' restated on
;;; NOT (= p (ZERO (POLY a))).  The move at the point of use is three lines --
;;; `prop' contraposes the bridge's backward half (both sides are opaque atoms
;;; to it, so this is pure propositional logic), and `push-not-h' (push-not.scm)
;;; turns the resulting NOT-of-a-guarded-universal into the guarded existential
;;; the pointwise theorem wants, in ONE move and with the guard never negated.
;;; Without `push-not-h' that step is the ~40 generic lines its own header
;;; describes.
;;;
;;; Needs: structure-library/polynomial (MONALG-ZERO, POLY), poly-membership
;;; (poly-membership), sqn (sqn-membership), ring (ring-zero-in),
;;; equality-basics (eq-sym, eq-trans), numeric-instances (nn-add-monoid@carr,
;;; fired by `slot' / `slot-h' and never by name).  Loaded after monalg-laws and
;;; before structure-library/poly-degree.
;;;
;;; Driver helpers are `pz-' prefixed: a top-level define named like a tactic
;;; silently rebinds it (CLAUDE.md, "Case folding").

;;; Peel the whole FORALL/IMPLIES prefix -- never a fixed count of `di's, which
;;; is greedy and would run past into a NOT.
(define (pz-peel!)
  (let loop ((k 0))
    (if (> k 12) (error "pz-peel!: runaway"))
    (if (memq (car (dk-goal)) '(forall implies))
        (begin (di) (loop (+ k 1))))))

;;; The two shapes the bridge is about, built once.
(define pz-ptwise '(FORALL k_ (IMPLIES (IN k_ NN) (= (p_ k_) (ZERO a_)))))
(define pz-zp     '(ZERO (POLY a_)))

;;; Split an IFF goal and drive each half.  The forward leaf is the one whose
;;; goal is the universal -- discriminated on the GOAL, never on the order
;;; `dk-opened' happens to return.
(define (pz-iff! fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'forall)) ls)) (fwd)
    (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'forall))) ls)) (bwd)))

;;; =====================================================================
;;; the pointwise value of the zero of A[M]
;;; =====================================================================

(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL x_
   (IMPLIES (IN x_ (CARR m_))
     (== ((MONALG-ZERO a_ m_) x_) (ZERO a_))))))))
(di) (mac 'MONALG-ZERO) (lam-b) (qrfl)
(qed 'monalg-zero-apply)
(gloss! 'monalg-zero-apply
  "0(x) = ZERO(A) for x in CARR(M): the defining value of the zero of the monoid
   algebra A[M], which is the constant zero function.  The twin of
   monalg-add-apply.")
(topic! 'monalg-zero-apply 'algebra)

;;; =====================================================================
;;; the zero of A[M] is a function on CARR(M)
;;; =====================================================================
;;;
;;; `lam-t' opens TWO leaves (CLAUDE.md): the pointwise typing of the body --
;;; here the constant ZERO(A), so the guard alone closes it -- and the SETHOOD
;;; of the domain.  A driver expecting one leaf leaves the other open and finds
;;; out at `qed'.

(sp (make-wff '(FORALL a_ (FORALL m_
   (IMPLIES (IN (CARR m_) SET)
     (IMPLIES (IN (ZERO a_) (CARR a_))
       (IN (MONALG-ZERO a_ m_) (FUN (CARR m_) (CARR a_)))))))))
(pz-peel!)
(mac 'MONALG-ZERO)
(for-each
  (lambda (l)
    (dk-focus! l)
    (if (equal? (dk-goal-of l) '(in (carr m_) set))
        (ass)
        (begin (di) (ass))))
  (dk-opened (lambda () (lam-t))))
(qed 'monalg-zero-fun)
(gloss! 'monalg-zero-fun
  "The zero of the monoid algebra A[M] is a function CARR(M) -> CARR(A).
   Guarded on the sethood of CARR(M) and on ZERO(A) lying in CARR(A) rather
   than on IS-MONOID/IS-RING, so that a concretely-known carrier (NN, for
   polynomials) can discharge it directly.")
(topic! 'monalg-zero-fun 'algebra)

;;; =====================================================================
;;; the zero of A[x], as a term and pointwise
;;; =====================================================================

(sp (make-wff '(FORALL a_ (== (ZERO (POLY a_)) (MONALG-ZERO a_ NN-ADD-MONOID)))))
(di) (mac 'POLY) (mac 'MONALG) (slot 'ZERO) (nth-r) (qrfl)
(qed 'poly-zero-unfold)
(gloss! 'poly-zero-unfold
  "The zero of POLY(A) is MONALG-ZERO(A, NN-ADD-MONOID), the constant zero
   coefficient sequence: POLY unfolds to MONALG, MONALG to the RING 6-tuple,
   and ZERO projects slot 5.")
(topic! 'poly-zero-unfold 'algebra)

;;; The STRICT equality, and the only statement in the file that needs IS-RING.
;;; It needs it for DEFINEDNESS and nothing else: `rfl' closes (ZERO a) =
;;; (ZERO a) only when some assumption witnesses that ZERO(a) is defined, and
;;; `ring-zero-in' is that assumption.
(sp (make-wff '(FORALL a_ (FORALL k_
   (IMPLIES (IS-RING a_)
     (IMPLIES (IN k_ NN)
       (= ((ZERO (POLY a_)) k_) (ZERO a_))))))))
(pz-peel!)
(fact 'ring-zero-in 'a_)
;; the guard monalg-zero-apply wants, in the spelling it wants it: `slot' fires
;; the nn-add-monoid@carr instance macete, which is never cited by name.
(have! '(IN k_ (CARR NN-ADD-MONOID)) (lambda () (slot 'CARR) (ass)))
(mac 'poly-zero-unfold)
(mac 'monalg-zero-apply)
(rfl)
(qed 'poly-zero-apply)
(gloss! 'poly-zero-apply
  "Every coefficient of the zero polynomial is ZERO(A): (ZERO(POLY A))(k) =
   ZERO(A) for k in NN.  Strict equality -- the definedness comes from
   ring-zero-in.")
(topic! 'poly-zero-apply 'algebra)

(sp (make-wff '(FORALL a_ (IMPLIES (IS-RING a_)
   (IN (ZERO (POLY a_)) (FUN NN (CARR a_)))))))
(pz-peel!)
(have! '(IN (CARR NN-ADD-MONOID) SET) (lambda () (slot 'CARR) (ta 'nn-is-set) (ass)))
(fact 'ring-zero-in 'a_)
(fact 'monalg-zero-fun 'a_ 'NN-ADD-MONOID)
(slot-h 'CARR '(IN (MONALG-ZERO a_ NN-ADD-MONOID) (FUN (CARR NN-ADD-MONOID) (CARR a_))))
(mac 'poly-zero-unfold)
(ass)
(qed 'poly-zero-fun)
(gloss! 'poly-zero-fun
  "The zero polynomial is a sequence: ZERO(POLY(A)) in FUN(NN, CARR(A)).  The
   typing fun-domain-extensionality asks for on the right-hand side of the
   bridge.")
(topic! 'poly-zero-fun 'algebra)

;;; =====================================================================
;;; poly-zero-iff -- THE BRIDGE
;;; =====================================================================
;;;
;;; A polynomial IS the zero polynomial exactly when all its coefficients
;;; vanish.  The one statement of its shape this layer gets; everything else
;;; that wants "these two agree pointwise, hence they are equal" cites
;;; `fun-domain-extensionality' directly, as the backward direction below does.

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'p_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN p_ (CARR (POLY a_)))
       (list 'IFF '(= p_ (ZERO (POLY a_))) pz-ptwise)))))))
(pz-peel!)

;; p is a function on NN: poly-membership gives SQN(CARR A), sqn-membership
;; spells that FUN(NN, CARR A), and fun-codomain-iff drops the codomain.
;; `mac-h' + `dk-split!' rather than `prop': by this point the citation chains
;; put 16 distinct atoms in the context against a cap of 12.
(mac-h 'poly-membership '(IN p_ (CARR (POLY a_))))
(dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
(mac-h 'sqn-membership '(IN p_ (SQN (CARR a_))))
(mac-h 'fun-codomain-iff '(IN p_ (FUN NN (CARR a_))))
(dk-split! (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'and)
                                      (equal? (cadr f) '(in p_ (fun nn)))))
                     (dk-asms)))

;; and so is the zero polynomial.
(fact 'poly-zero-fun 'a_)
(mac-h 'fun-codomain-iff (list 'IN pz-zp '(FUN NN (CARR a_))))
(dk-split! (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'and)
                                      (equal? (cadr f) (list 'in pz-zp '(fun nn)))))
                     (dk-asms)))

(pz-iff!
  ;; ---- => : substitute the equation and compute ------------------------
  ;; The substitution reaches p in OPERATOR position because p is a bare
  ;; SYMBOL; see the header.
  (lambda ()
    (di)
    (subst '(= p_ (ZERO (POLY a_))))
    (fact 'poly-zero-apply 'a_ 'k_)
    (ass))
  ;; ---- <= : fun-domain-extensionality ----------------------------------
  (lambda ()
    (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
              (list '= '(p_ k_) (list pz-zp 'k_))))
      (lambda ()
        (di)
        (fact 'poly-zero-apply 'a_ 'k_)
        (fact 'eq-sym (list pz-zp 'k_) '(ZERO a_))
        (dk-deepest (lambda () (inst+ pz-ptwise 'k_)))
        (fact 'eq-trans '(p_ k_) '(ZERO a_) (list pz-zp 'k_))
        (ass)))
    (fact 'fun-domain-extensionality 'NN 'p_ pz-zp)
    (ass)))
(qed 'poly-zero-iff)
(gloss! 'poly-zero-iff
  "A polynomial over A is the zero polynomial exactly when every one of its
   coefficients is ZERO(A).  The extensionality bridge for POLY: the backward
   direction is fun-domain-extensionality at NN, the forward direction is
   substitution plus poly-zero-apply.  Contraposed, it turns `p /= 0' into
   `some coefficient of p is nonzero', which is the hypothesis every pointwise
   statement about polynomials actually consumes.")
(topic! 'poly-zero-iff 'algebra)
