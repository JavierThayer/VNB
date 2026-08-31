;;; normed-field-ring-view.scm -- THE SCALAR BRIDGE, PROVEN.
;;;
;;; NORMED-FIELD is a 7-slot shape (carrier, the five ring operations, NRM at
;;; slot 7) and the ring predicates pin length(s)=6, so a normed field reaches
;;; the ring world only through the projection
;;;
;;;     NORMED-FIELD-AS-COMMUTATIVE-RING(f) = [carr(f), add(f), mul(f),
;;;                                            neg(f), zero(f), one(f)]
;;;
;;; (views.scm:167).  That projection is what a scalar SLOT must hold -- see
;;; structure-library/normed-vector-space.scm and complex-inner-product.scm,
;;; both of which pin their scalars to it -- and it is therefore what every law
;;; of those structures reads its scalars THROUGH: `carr(scal(s))',
;;; `add(scal(s))', `mul(scal(s))', `one(scal(s))'.
;;;
;;; WHAT WAS MISSING.  `def-functor' installs a functoid and a typing axiom and
;;; nothing else, so before this file NOTHING in the tree said what
;;; `carr(normed-field-as-commutative-ring(rr-normed-field))' IS.  A proof that
;;; reached a normed vector space's scalars had to unfold the functoid in the
;;; goal by hand and then reduce an NTH against a six-element LIST literal --
;;; and could not do it at all on a HYPOTHESIS, a functoid having no theorem for
;;; `mac-h' to rebuild a rule from (CLAUDE.md, "Where a definition lives").
;;;
;;; NOTHING HERE IS ASSERTED.  Each statement is the functoid unfold composed
;;; with an NTH projection -- both trusted base -- and each is proved in five
;;; steps, `proven modulo 0':
;;;
;;;     (slot ACC)          the accessor down to its NTH projection
;;;     (mac  'NORMED-FIELD-AS-COMMUTATIVE-RING)   the functoid unfold
;;;     (nth-r)             NTH k of a LIST literal
;;;     (slot ACC)          the recovered source accessor -- at an INSTANCE this
;;;                         fires that instance's value macete and finishes
;;;     (qrfl)
;;;
;;; `==' (not `='): the projection's slot value is unconditionally that term, so
;;; no definedness obligation is owed -- the same choice declare-instance! makes
;;; for its own slot equations (structures.scm:387 ff.).
;;;
;;; TWO LAYERS, and the second is the one proofs cite.  The GENERIC read-offs
;;; hold for any normed field and serve RR and CC alike; the RR-NORMED-FIELD
;;; instances compose them with the instance value macetes minted by
;;; `declare-instance!' (numeric-instances.scm:250) and land on the surface
;;; language -- RR, binplus, bintimes, binneg, 0, 1 -- which is what a proof
;;; about a real normed vector space actually wants to see.
;;;
;;; Dependencies: views.scm (NORMED-FIELD-AS-COMMUTATIVE-RING),
;;; numeric-instances.scm (RR-NORMED-FIELD and its six value macetes),
;;; interactive + proof-debt.  No structure of this file's own.

;;; ---- file-local driver (the `nfrv-' prefix; `slot' is a tactic, not a name
;;; ---- we may bind, and single/double capitals are the case-fold danger zone).

;;; The five-step proof, once.  ACC is the accessor, TERM the tuple it is read
;;; off, VAL the value claimed.  Errors if the proof does not close -- a silent
;;; no-op here would install nothing and say nothing.
(define (nfrv-prove! name acc term val)
  (sp (make-wff (list '== (list acc term) val)))
  (slot acc)
  (mac 'NORMED-FIELD-AS-COMMUTATIVE-RING)
  (nth-r)
  (slot acc)
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "nfrv-prove!: proof did not close" name (dk-goal)))
  (qed name))

;;; The same, universally quantified over the normed field.  One extra `di' to
;;; peel the binder, and the closing `slot' takes the recovered (ACC f_) to its
;;; NTH projection rather than to a value -- f_ is a variable, so there is no
;;; instance macete to fire and the generic projection is what closes it.
(define (nfrv-prove-generic! name acc)
  (sp (make-wff (list 'FORALL 'f_
                  (list '== (list acc (list 'NORMED-FIELD-AS-COMMUTATIVE-RING 'f_))
                            (list acc 'f_)))))
  (di)
  (slot acc)
  (mac 'NORMED-FIELD-AS-COMMUTATIVE-RING)
  (nth-r)
  (slot acc)
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "nfrv-prove-generic!: proof did not close" name (dk-goal)))
  (qed name))

;;; =====================================================================
;;; (1) GENERIC -- the ring view of ANY normed field, slot by slot.
;;; =====================================================================

(nfrv-prove-generic! 'normed-field-ring-view-carr 'CARR)
(topic! 'normed-field-ring-view-carr 'algebra)

(nfrv-prove-generic! 'normed-field-ring-view-add  'ADD)
(topic! 'normed-field-ring-view-add 'algebra)

(nfrv-prove-generic! 'normed-field-ring-view-mul  'MUL)
(topic! 'normed-field-ring-view-mul 'algebra)

(nfrv-prove-generic! 'normed-field-ring-view-neg  'NEG)
(topic! 'normed-field-ring-view-neg 'algebra)

(nfrv-prove-generic! 'normed-field-ring-view-zero 'ZERO)
(topic! 'normed-field-ring-view-zero 'algebra)

(nfrv-prove-generic! 'normed-field-ring-view-one  'ONE)
(topic! 'normed-field-ring-view-one 'algebra)

;;; =====================================================================
;;; (2) AT THE REALS -- the tuple a real normed vector space's SCAL slot holds.
;;;
;;; These are the bridge `normed-vector-space.scm' needs: its laws quantify
;;; `r_ in carr(scal(s))' and apply `add(scal(s))' / `mul(scal(s))' /
;;; `one(scal(s))', and with the scalars pinned to
;;; NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD) each of those is one
;;; `subst' of the pinning law away from the six equations below.
;;; =====================================================================

(nfrv-prove! 'rr-scalar-ring-carr 'CARR
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) 'RR)
(topic! 'rr-scalar-ring-carr 'algebra)

;;; 2026-08-29: the value was the shared constant `binplus'.  RR-NORMED-FIELD's
;;; ADD slot now holds a tupled VNB-LAMBDA instead -- one function per instance,
;;; rather than one object asserted into five function classes at once (which
;;; proved ZZ = QQ = RR = CC and thence FALSITY; see numeric-instances.scm).
;;; The equation is the same KIND of fact and proves by the same five steps; only
;;; the right-hand side moved.
(nfrv-prove! 'rr-scalar-ring-add 'ADD
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
             '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)))
(topic! 'rr-scalar-ring-add 'algebra)

(nfrv-prove! 'rr-scalar-ring-mul 'MUL
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
             '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (* x_ y_)))
(topic! 'rr-scalar-ring-mul 'algebra)

(nfrv-prove! 'rr-scalar-ring-neg 'NEG
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
             '(VNB-LAMBDA x_ RR (- x_)))
(topic! 'rr-scalar-ring-neg 'algebra)

(nfrv-prove! 'rr-scalar-ring-zero 'ZERO
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) 0)
(topic! 'rr-scalar-ring-zero 'algebra)

(nfrv-prove! 'rr-scalar-ring-one 'ONE
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) 1)
(topic! 'rr-scalar-ring-one 'algebra)
