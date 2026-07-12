;;; reduce.scm -- REDUCE: left-fold of a binary op over a finite indexed
;;; family.  Bridges the kiddie n-ary surface form (+ x y z ...) and the
;;; adult finite-sum operator SUM-AG.
;;;
;;;   (REDUCE op f n)  =  op( op( ... op(f(0), f(1)) ..., f(n-2) ), f(n-1) )
;;;
;;; for n >= 1; undefined for n = 0 (no identity argument).  The left-fold
;;; matches the bracketing the parser uses for chained n-ary infix:
;;;   x + y + z   ==   (binplus (binplus x y) z)
;;; with f(0)=x, f(1)=y, f(2)=z this is exactly (REDUCE binplus f 3).
;;;
;;; The kiddie surface (+ x_1 ... x_n) bridges to
;;;   (REDUCE binplus (FAM-OF-LIST (LIST x_1 ... x_n)) n)
;;; via the nary-plus-N-list axioms in numeric-instances.scm; the adult
;;; finite-sum SUM-AG bridges to (REDUCE (OPR ag) f n) for n >= 1 via
;;; sum-ag-as-reduce in sequences.scm.  The n = 0 case is purely SUM-AG's
;;; (SUM-AG(ag,f,0) = IDEN(ag)); REDUCE has no counterpart there.
;;;
;;; Why both bridges live (rather than replacing nary-plus-N with the list
;;; form): nary-plus-N -> nested binplus stays the natural rewrite when a
;;; proof is using the structure-library RING operators ((ADD R) = binplus);
;;; nary-plus-N-list -> REDUCE is the natural rewrite when a proof is
;;; reaching for SUM-AG-style finite-sum machinery.  Same kiddie surface,
;;; two downstream paths.

;;; -----------------------------------------------------------------------
;;; FAM-OF-LIST: turn a 1-indexed VNB LIST into a 0-indexed family over
;;; ORD-SEGMENT(LENGTH L), absorbing the off-by-one between NTH (1-based)
;;; and seg/SUM-AG (0-based) in one place.
;;;
;;;   (FAM-OF-LIST L) i  =  NTH(succ i, L)   for 0 <= i < LENGTH L
;;;
;;; The codomain typing (FUN (ORD-SEGMENT (LENGTH L)) A) is left for a
;;; later axiom when a caller needs the FUN membership; the apply axiom
;;; alone covers the kiddie/REDUCE bridges.

(def-constant 'FAM-OF-LIST
  '(fam-of-list-apply
    (FORALL L
      (FORALL i
        (IMPLIES (AND (IN i NN) (<= (succ i) (LENGTH L)))
                 (= ((FAM-OF-LIST L) i) (NTH (succ i) L)))))))

;;; -----------------------------------------------------------------------
;;; REDUCE: characterizing axioms.
;;;
;;;   reduce-one:   (REDUCE op f 1) = (f 0)
;;;   reduce-succ:  (REDUCE op f (succ n)) = (op (REDUCE op f n) (f n))     for n >= 1
;;;
;;; The step guard (<= 1 n) keeps it from firing at n = 0, so VNB's
;;; partial-equality semantics never have to reconcile the base reduce-one
;;; with a putative right-hand side (op (REDUCE op f 0) (f 0)) whose left
;;; operand is undefined.  REDUCE is genuinely partial at n = 0; that's the
;;; whole point -- the caller chooses an identity by lifting to SUM-AG.

(def-constant 'REDUCE
  '(reduce-one
    (FORALL op
      (FORALL f
        (== (REDUCE op f 1) (f 0)))))
  '(reduce-succ
    (FORALL op
      (FORALL f
        (FORALL n
          (IMPLIES (AND (IN n NN) (<= 1 n))
                   (== (REDUCE op f (succ n))
                      (op (REDUCE op f n) (f n)))))))))
