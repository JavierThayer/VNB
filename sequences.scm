;;; sequences.scm -- PROD-ORD and SUM: products and sums over initial NN-segments
;;;
;;; PROD-ORD(m, f, n)  =  f(0) * f(1) * ... * f(n-1)  in monoid m
;;; SUM(r, f, n)       =  f(0) + f(1) + ... + f(n-1)  in ring r
;;;
;;; Both are defined by primitive recursion on the last argument n.
;;; The defining axioms (<name>-zero, <name>-succ) are installed by
;;; def-by-nn-recursion; further axioms are installed explicitly below.
;;;
;;; Dependencies: algebraic.scm (IS-MONOID, A, MUL, E, IS-RING, ADD, ZERO),
;;;               number-systems.scm (NN).

;;; -----------------------------------------------------------------------
;;; PROD-ORD: monoid product over {0, ..., n-1}

;;; Defining recursion (installs prod-ord-zero and prod-ord-succ):
;;;   PROD-ORD(m, f, 0)       = E(m)
;;;   PROD-ORD(m, f, succ(n)) = PROD-ORD(m, f, n) * f(n)

(def-by-nn-recursion 'PROD-ORD '(m f)
  '(E m)                              ; base value
  '(n val)                            ; step vars: n ∈ NN, val = PROD-ORD(m,f,n)
  '((MUL m) val (f n)))               ; PROD-ORD(m,f,succ n) = val * f(n)

;;; Type: result is in the carrier when m is a monoid and f maps NN into it.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from prod-ord-zero,
;;; prod-ord-succ, monoid-left-id, and monoid-carrier-closed-mul.  Installed
;;; as an axiom for direct use; eventually demote to a proven lemma.
(theory-add-axiom! *current-theory* 'prod-ord-type
  '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (A m)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (PROD-ORD m f n) (A m)))))))))

;;; Singleton: PROD-ORD(m, f, 1) = f(0).
;;; DERIVED (REVIEW.md R-10): prod-ord-succ at n=0 gives
;;; (MUL m)(E m)(f 0), then monoid-left-id closes to (f 0).  Installed
;;; as an axiom for direct use.
(theory-add-axiom! *current-theory* 'prod-ord-singleton
  '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (A m)))
                          (= (PROD-ORD m f 1) (f 0)))))))

;;; -----------------------------------------------------------------------
;;; SUM: ring summation over {0, ..., n-1}
;;;
;;; SUM is the special case of PROD-ORD for the additive monoid of a ring:
;;;   MUL  ->  ADD(r)
;;;   E    ->  ZERO(r)
;;; Defined independently to avoid introducing an explicit ADD-MONOID record.

;;; Defining recursion (installs sum-zero and sum-succ):
;;;   SUM(r, f, 0)       = ZERO(r)
;;;   SUM(r, f, succ(n)) = SUM(r, f, n) + f(n)

(def-by-nn-recursion 'SUM '(r f)
  '(ZERO r)                           ; base value
  '(n val)                            ; step vars
  '((ADD r) val (f n)))               ; SUM(r,f,succ n) = val + f(n)

;;; Type: result is in the carrier.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from sum-zero, sum-succ,
;;; ring-zero-in, and ring-carrier-closed-add.  Installed for direct use.
(theory-add-axiom! *current-theory* 'sum-type
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (A r)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (SUM r f n) (A r)))))))))

;;; Singleton: SUM(r, f, 1) = f(0).
;;; DERIVED (REVIEW.md R-10): sum-succ at n=0 gives (ADD r)(ZERO r)(f 0),
;;; then a ring's left-zero-add identity closes to (f 0).  Installed for direct use.
(theory-add-axiom! *current-theory* 'sum-singleton
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (A r)))
                          (= (SUM r f 1) (f 0)))))))

;;; -----------------------------------------------------------------------
;;; RING-PROD-N: n-fold ring product
;;;
;;; RING-PROD-N(f, n) = f(0) × f(1) × ... × f(n-1)  as a ring.
;;; Defined by primitive recursion on n using RING-PROD and ZERO-RING.
;;;
;;; The 0-fold product is ZERO-RING (the terminal ring, identity for ×
;;; up to isomorphism).  Each step wraps the accumulated product with
;;; the next ring in the sequence.
;;;
;;; (REVIEW.md G-6) When the hypothesis "all f(i) are rings" fails, the
;;; resulting term is still a syntactically well-formed 6-LIST whose
;;; components may be junk.  Soundness is preserved because the typing
;;; claim ring-prod-n-is-ring then simply doesn't apply (its IS-RING
;;; antecedent is false), so no false ring identity can be derived from
;;; the junk.  Users should not destructure RING-PROD-N(f, n) without
;;; first proving the hypothesis.
;;;
;;; Dependencies: algebraic.scm (RING-PROD, ZERO-RING, IS-RING).

(def-by-nn-recursion 'RING-PROD-N '(f)
  'ZERO-RING                           ; base: RING-PROD-N(f, 0) = ZERO-RING
  '(n val)                             ; step vars
  '(RING-PROD val (f n)))              ; RING-PROD-N(f, succ n) = RING-PROD(val, f(n))

;;; Typing: all f(i) are rings → RING-PROD-N(f, n) is a ring.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from ring-prod-is-ring
;;; (step) + zero-ring-is-ring (base).  Installed as an axiom for direct use.
(theory-add-axiom! *current-theory* 'ring-prod-n-is-ring
  '(FORALL f
      (FORALL n (IMPLIES (IN n NN)
        (IMPLIES (FORALL i (IMPLIES (IN i NN) (IS-RING (f i))))
          (IS-RING (RING-PROD-N f n)))))))

;;; Linearity (left scalar pull-out):
;;; SUM(r, lambda i. a * f(i), n) = a * SUM(r, f, n)
;;; Stated schematically for inline use (derivable by induction + distributivity).
;;; The VNB-LAMBDA form below uses the built-in lambda binder.
(theory-add-axiom! *current-theory* 'sum-left-scalar
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL a
                 (IMPLIES (IN a (A r))
                          (FORALL f
                            (IMPLIES (IN f (FUN NN (A r)))
                                     (FORALL n
                                       (IMPLIES (IN n NN)
                                         (= (SUM r (VNB-LAMBDA i ((MUL r) a (f i))) n)
                                            ((MUL r) a (SUM r f n))))))))))))
