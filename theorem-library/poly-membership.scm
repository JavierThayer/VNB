;;; poly-membership.scm -- SUPP / FINSUPP / POLY read-offs, PROVEN.
;;;
;;; WHAT IS HERE.  The membership characterisations of the three SEP-bodied
;;; constructors of structure-library/polynomial.scm --
;;;
;;;     SUPP(A,M,f)   = { x in CARR(M) : f(x) /= ZERO(A) }
;;;     FINSUPP(A,M)  = { f in FUN(CARR M, CARR A) : CARD(SUPP(A,M,f)) in NN }
;;;     POLY(A)       = MONALG(A, NN-ADD-MONOID)
;;;
;;; -- as citable IFFs, plus the unfolding equations that produce them and the
;;; sethood of a support.  Nothing here is asserted: every statement is
;;; `proven modulo 0'.
;;;
;;; WHY THE FILE EXISTS.  `def-functoid' installs only a rewrite MACETE, not a
;;; theorem, so `mac' unfolds FINSUPP in a GOAL but `mac-h' CANNOT unfold it in
;;; an ASSUMPTION: it warns `unknown theorem/macete' and the driver sails on
;;; with the hypothesis untouched (verified for FINSUPP, 2026-08-20).  A
;;; polynomial is always read OUT of a context -- "let f be a polynomial" -- so
;;; without a citable membership law nothing can be said about one.
;;;
;;; THE RECIPE, and it needs no new axiom.  Prove the unfolding equation once:
;;; the functoid macete DOES apply to a goal that IS the equation, so
;;;
;;;     (sp ...(== (FINSUPP a_ m_) (SEP f_ ...)))  (di) (mac 'FINSUPP) (qrfl)
;;;
;;; is the whole proof.  The result is a THEOREM, and `mac-h' rebuilds its rule
;;; from the theorem table -- so `(mac-h 'finsupp-unfold h)' turns the
;;; hypothesis into a literal SEP membership, which the kernel's `sep-me' then
;;; reads apart.  interval-basics.scm reaches the same place by `have!' +
;;; `subst'; the `mac-h' route is one step and works on the hypothesis in place.
;;;
;;; `==' (not `='), and for interval-basics' reason: `rfl' carries a definedness
;;; side-condition and a bare SEP term is not syntactically defined, so `=' would
;;; owe a witness it does not need.  `qrfl' closes the `=='.
;;;
;;; CONSEQUENCE FOR THE `definitional'-STAMP PRACTICE.  CLAUDE.md's rule --
;;; "any SEP-bodied def-functoid whose members get read out of the context wants
;;; a membership IFF stated beside it and wrapped `definitional'" -- buys with a
;;; stipulation what this file gets for nothing.  `span-membership' (mod-seq),
;;; `principal-ideal-membership' (ideal), `sqn-membership' (sqn) and the five in
;;; definitional-reclass are all of this shape and all provable the same way.
;;; Left alone here: re-tiering a stamped fact moves every citing bill, and that
;;; is a separate measurement.
;;;
;;; NAMING.  Binders are `a_ m_ f_ x_' throughout.  polynomial.scm:52 records
;;; why the evaluation point is `x_' and never `m': `m' case-folds onto the
;;; monoid parameter M and would capture it.

;;; Split an IFF goal into its two implications and drive each.  The forward
;;; leaf is the one whose GOAL is the conjunction -- discriminated on the goal,
;;; never on the order `dk-opened' happens to return.
(define (plm-iff! fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'and)) ls)) (fwd)
    (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'and))) ls)) (bwd)))

;;; =====================================================================
;;; SUPP -- the support of f, a SEP over CARR(M)
;;; =====================================================================

(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_
   (== (SUPP a_ m_ f_) (SEP x_ (CARR m_) (NOT (= (f_ x_) (ZERO a_))))))))))
(di) (mac 'SUPP) (qrfl)
(qed 'supp-unfold)
(gloss! 'supp-unfold
  "SUPP(A,M,f) is the separation { x in CARR(M) : f(x) /= ZERO(A) }, as a citable
   equation.  Cite it with mac-h to open a support membership in a hypothesis.")
(topic! 'supp-unfold 'plumbing)

;;; x is in the support iff it is a point of M where f does not vanish.
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_ (FORALL x_
   (IFF (IN x_ (SUPP a_ m_ f_))
        (AND (IN x_ (CARR m_)) (NOT (= (f_ x_) (ZERO a_)))))))))))
(di)
(plm-iff!
  ;; => : rewrite the hypothesis into the SEP, read both halves off it, and let
  ;; `prop' assemble the conjunction from them.
  (lambda ()
    (mac-h 'supp-unfold '(IN x_ (SUPP a_ m_ f_)))
    (sep-me '(IN x_ (SEP x_ (CARR m_) (NOT (= (f_ x_) (ZERO a_))))))
    (prop))
  ;; <= : unfold the GOAL and discharge sep-mi's two obligations from the split
  ;; conjunction.
  (lambda ()
    (dk-split! '(AND (IN x_ (CARR m_)) (NOT (= (f_ x_) (ZERO a_)))))
    (mac 'SUPP)
    (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))))
(qed 'supp-membership)
(gloss! 'supp-membership
  "x lies in SUPP(A,M,f) iff x is a point of CARR(M) at which f(x) is not the
   zero of A.  The read-off of the support, in both directions.")
(topic! 'supp-membership 'algebra)

;;; A support is a set: it is a separation over CARR(M), so CARR(M) being a set
;;; is the whole hypothesis.  (Stated with that hypothesis rather than derived
;;; from IS-MONOID: the sethood of a structure's carrier is a separate question,
;;; and this way the lemma is usable wherever the carrier is known concretely --
;;; which is the polynomial case, CARR(NN-ADD-MONOID) = NN.)
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_
   (IMPLIES (IN (CARR m_) SET) (IN (SUPP a_ m_ f_) SET)))))))
(di) (di) (mac 'SUPP) (sep-set) (ass)
(qed 'supp-in-set)
(gloss! 'supp-in-set
  "The support of f is a set whenever CARR(M) is: it is a separation over it.")
(topic! 'supp-in-set 'plumbing)

;;; =====================================================================
;;; FINSUPP -- the carrier of the monoid algebra
;;; =====================================================================

(sp (make-wff '(FORALL a_ (FORALL m_
   (== (FINSUPP a_ m_)
       (SEP f_ (FUN (CARR m_) (CARR a_)) (IN (CARD (SUPP a_ m_ f_)) NN)))))))
(di) (mac 'FINSUPP) (qrfl)
(qed 'finsupp-unfold)
(gloss! 'finsupp-unfold
  "FINSUPP(A,M) is the separation { f in FUN(CARR M, CARR A) : SUPP(A,M,f) is
   finite }, as a citable equation.")
(topic! 'finsupp-unfold 'plumbing)

;;; THE readout: f is an element of the monoid algebra's carrier iff it is a
;;; function on CARR(M) valued in CARR(A) whose support is finite.
(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_
   (IFF (IN f_ (FINSUPP a_ m_))
        (AND (IN f_ (FUN (CARR m_) (CARR a_)))
             (IN (CARD (SUPP a_ m_ f_)) NN))))))))
(di)
(plm-iff!
  (lambda ()
    (mac-h 'finsupp-unfold '(IN f_ (FINSUPP a_ m_)))
    (sep-me '(IN f_ (SEP f_ (FUN (CARR m_) (CARR a_)) (IN (CARD (SUPP a_ m_ f_)) NN))))
    (prop))
  (lambda ()
    (dk-split! '(AND (IN f_ (FUN (CARR m_) (CARR a_)))
                     (IN (CARD (SUPP a_ m_ f_)) NN)))
    (mac 'FINSUPP)
    (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))))
(qed 'finsupp-membership)
(gloss! 'finsupp-membership
  "f belongs to FINSUPP(A,M) -- the carrier of the monoid algebra A[M] -- iff f
   is a function from CARR(M) to CARR(A) whose support is finite.")
(topic! 'finsupp-membership 'algebra)

;;; =====================================================================
;;; POLY -- one-variable polynomials, A[NN]
;;; =====================================================================

;;; The carrier of POLY(A).  POLY unfolds to MONALG, MONALG to the RING 6-tuple,
;;; and CARR projects slot 1 -- three trusted rewrites and `nth-r'.
(sp (make-wff '(FORALL a_ (== (CARR (POLY a_)) (FINSUPP a_ NN-ADD-MONOID)))))
(di) (mac 'POLY) (mac 'MONALG) (slot 'CARR) (nth-r) (qrfl)
(qed 'poly-carrier)
(gloss! 'poly-carrier
  "The carrier of POLY(A) is FINSUPP(A, NN-ADD-MONOID): the finitely-supported
   coefficient sequences NN -> CARR(A).")
(topic! 'poly-carrier 'algebra)

;;; THE statement the user asks for, in the SQN vocabulary: a polynomial over A
;;; is a SEQUENCE in CARR(A) -- an element of SQN(CARR A) = FUN(NN, CARR A) --
;;; with finitely many non-zero coefficients.  `sqn-membership' bridges the two
;;; spellings, and `slot' / `slot-h' turn the monoid's carrier into NN by firing
;;; the instance macete nn-add-monoid@carr (carr(NN-ADD-MONOID) == NN, installed
;;; by declare-instance!).  NOT `mac' / `mac-h' on that name: the suite pins that
;;; an accessor macete is never fired by name outside `slot' ("no file fires an
;;; accessor macete by name"), and firing it by name is what makes the pin fail.
(sp (make-wff '(FORALL a_ (FORALL f_
   (IFF (IN f_ (CARR (POLY a_)))
        (AND (IN f_ (SQN (CARR a_)))
             (IN (CARD (SUPP a_ NN-ADD-MONOID f_)) NN)))))))
(di)
(plm-iff!
  (lambda ()
    (mac-h 'poly-carrier '(IN f_ (CARR (POLY a_))))
    (mac-h 'finsupp-membership '(IN f_ (FINSUPP a_ NN-ADD-MONOID)))
    (dk-split! '(AND (IN f_ (FUN (CARR NN-ADD-MONOID) (CARR a_)))
                     (IN (CARD (SUPP a_ NN-ADD-MONOID f_)) NN)))
    (slot-h 'CARR '(IN f_ (FUN (CARR NN-ADD-MONOID) (CARR a_))))
    (have! '(IN f_ (SQN (CARR a_))) (lambda () (mac 'sqn-membership) (ass)))
    (prop))
  (lambda ()
    (dk-split! '(AND (IN f_ (SQN (CARR a_)))
                     (IN (CARD (SUPP a_ NN-ADD-MONOID f_)) NN)))
    (mac-h 'sqn-membership '(IN f_ (SQN (CARR a_))))
    (mac 'poly-carrier) (mac 'finsupp-membership) (slot 'CARR)
    (prop)))
(qed 'poly-membership)
(gloss! 'poly-membership
  "f is a polynomial over A -- an element of CARR(POLY(A)) -- iff f is a sequence
   in CARR(A) (an element of SQN(CARR A) = FUN(NN, CARR A)) with finite support,
   i.e. with only finitely many non-zero coefficients.")
(topic! 'poly-membership 'algebra)
