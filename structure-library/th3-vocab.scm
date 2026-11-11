;;; th3-vocab.scm -- wave of 2026-11-09/10 (agent TH3-A), wired 2026-11-10 from scratchpad/th3-1109/th3-vocab.scm.
;;; Library: operator-algebras.

;;; th3-vocab.scm -- COMPACT OPERATORS, HILBERT-SCHMIDT AND TRACE CLASS on complex Hilbert
;;; spaces.  F. J. Thayer, "Operadores ... / Analise funcional e teoria espectral"
;;; (docs/th-main.pdf), Def. 1.57, ch. 3 s.3.1-3.7.  DEFINITIONS ONLY: no proof, no support,
;;; no axiom.  The unfold and membership theorems are in th3-vocab-unfold.scm.
;;; Agent TH3-A, wave 2026-11-09.  Destination: structure-library/th3-vocab.scm.
;;; Library: operator-algebras (beside ba-ops-vocab, whose BOUNDED-OPS / OPNORM / OP-ADJOINT /
;;; BOP-* it uses).
;;; Load window: after structure-library/ba-ops-vocab (BOUNDED-OPS, BOP-COMP, OP-ADJOINT),
;;; structure-library/hilbert-onb-vocab (IS-ORTHONORMAL-BASIS), structure-library/
;;; l2-families-vocab (CC-FAMILY-SUM), structure-library/cauchy-subsequence (STRICTLY-MONO-NN),
;;; structure-library/metric-completeness (CONVERGES-TO), structure-library/extended-sum (ESUM).
;;;
;;; CONVENTIONS.  v, w are complex inner product spaces (in use: Hilbert spaces), the inner
;;; product linear in the FIRST argument, ||x|| = IP-NORM(v, x).  An operator is a member of
;;; FUN(VEC v, VEC w); K(H) is COMPACT-OPS(v, v).
;;;
;;; DECISIONS RECORDED HERE.
;;; 1. IS-COMPACT-OP is the SEQUENTIAL form of Def. 1.57 ("T(B_1) is relatively compact"):
;;;    every sequence in the closed unit ball has a subsequence whose image converges in w.
;;;    In a metric space a set is relatively compact iff every sequence in it has a subsequence
;;;    converging in the space, so this is Def. 1.57 for metric w; no completeness is used.
;;;    The operator is required to be BOUNDED (in BOUNDED-OPS(v, w)), which is the first half of
;;;    Prop. 1.59 (a compact linear operator is bounded) folded into the definition, as K(E, F)
;;;    is read as a subset of L(E, F) everywhere in ch. 3.
;;; 2. A FINITE-RANK operator is a finite sum of rank-one operators x |-> <x | a_k> b_k, the
;;;    form of Example 1.60.  For a bounded operator this is "dim ran T < infinity"; that
;;;    equivalence (Gram-Schmidt on the range) is a theorem to prove, not a definition.
;;; 3. The basis used to DEFINE a basis-free quantity (HS-NORM, HS-IP, OP-TRACE) is CANON-ONB(v),
;;;    the CHOICE of an orthonormal basis SET of v (indexed by itself).  ONB-SETS(v) is a set (a
;;;    subset of POWER(VEC v)), and it is inhabited for every complex inner product space
;;;    (onb-complete-orthonormal-set-exists, hilbert-onb.scm).  Independence of the basis is a
;;;    theorem (Obs. 3.35 / Prop. 3.37 / Prop. 3.45), stated with HS-SUM for an arbitrary ONB
;;;    (ix, e).
;;; 4. IS-HILBERT-SCHMIDT is Def. 3.34: SOME orthonormal basis (ix, e) has sum ||T e_i||^2
;;;    finite (HS-SUM real; HS-SUM is the ESUM in [0, +inf]).  The witnesses carry the guards
;;;    ix in SET and e in FUN(ix, VEC v) (redundant with IS-ORTHONORMAL-BASIS for e) because W1's
;;;    NBG check refuses a SEP (HS-OPS) whose condition has a binder not confined to sets.
;;; 5. TRACE CLASS is the characterization of Prop. 3.47, T = A B with A, B Hilbert-Schmidt
;;;    (the definition of BanachAlgebras.pdf Def. 2.13, and BA-MAP-REPORT.md s.3.7's plan), NOT
;;;    Def. 3.43 (|T|^{1/2} in HS), which needs the square root of a positive compact operator
;;;    before anything can be said.  Def. 3.43 <=> IS-TRACE-CLASS is a theorem to prove.
;;;    OP-TRACE (the symbol TRACE is taken by path-integral.scm) is Def. 3.46 on CANON-ONB.
;;; 6. IS-SELF-ADJOINT-OP is the book's s.3.1 reading, <T x | y> = <x | T y> for all x, y,
;;;    with T bounded; OP-ADJOINT(v, v, T) = T is a theorem away (op-adjoint-unique).
;;;    IS-POSITIVE-OP adds <T x | x> real and >= 0.  OP-SQRT is the IOTA of the positive
;;;    square root (it denotes once existence and uniqueness are proven, s.3.2);
;;;    ABS-OP(v, T) = |T| = OP-SQRT(v, T* T) (s.3.3).
;;; 7. EIGENSPACE(v, T, lam) is N_lambda(T) = ker(T - lam I) (s.3.1), as a SEP.
;;;
;;; Binders kq*_ (kqx_ kqy_ kqf_ kqn_ kqp_ kql_ kqi_ kqa_ kqb_ kqk_ kqo_ kqe_ kqs_), parameters
;;; kqv_ kqw_ kqt_ kqu_ kqm_ kqc_ kqj_ kqd_ kqg_ (functoid / predicate parameters); used by no
;;; other file.

;;; --------------------------------------------------------------------------------------------
;;; COMPACT OPERATORS (Def. 1.57, sequential form)
(def-predicate 'IS-COMPACT-OP '(kqv_ kqw_ kqt_)
  '(AND (IN kqt_ (BOUNDED-OPS kqv_ kqw_))
        (FORALL kqf_ (IMPLIES (IN kqf_ (FUN NN (VEC kqv_)))
          (IMPLIES (FORALL kqn_ (IMPLIES (IN kqn_ NN) (<= (IP-NORM kqv_ (kqf_ kqn_)) 1)))
            (FORSOME kqp_ (AND (STRICTLY-MONO-NN kqp_)
              (FORSOME kql_ (CONVERGES-TO (IP-METRIC-SPACE kqw_)
                              (VNB-LAMBDA kqn_ NN (kqt_ (kqf_ (kqp_ kqn_))))
                              kql_)))))))))

;;; K(v, w); K(H) = COMPACT-OPS(v, v)
(def-functoid 'COMPACT-OPS '(kqv_ kqw_)
  '(SEP kqt_ (BOUNDED-OPS kqv_ kqw_) (IS-COMPACT-OP kqv_ kqw_ kqt_)))

;;; --------------------------------------------------------------------------------------------
;;; FINITE RANK (Example 1.60)
;;; the rank-one operator x |-> <x | a> b  from v to w
(def-functoid 'RANK-ONE-OP '(kqv_ kqw_ kqa_ kqb_)
  '(VNB-LAMBDA kqx_ (VEC kqv_) ((ACT kqw_) ((IP kqv_) kqx_ kqa_) kqb_)))

;;; T x = sum_{k in kqi_} <x | a_k> b_k for a finite index set kqi_
(def-predicate 'IS-FINITE-RANK-OP '(kqv_ kqw_ kqt_)
  '(AND (IN kqt_ (BOUNDED-OPS kqv_ kqw_))
        (FORSOME kqi_ (AND (IN kqi_ SET) (AND (IN (CARD kqi_) NN)
          (FORSOME kqa_ (AND (IN kqa_ (FUN kqi_ (VEC kqv_)))
            (FORSOME kqb_ (AND (IN kqb_ (FUN kqi_ (VEC kqw_)))
              (FORALL kqx_ (IMPLIES (IN kqx_ (VEC kqv_))
                (= (kqt_ kqx_)
                   (FINSUM (NORMED-AG-AS-ABELIAN-GROUP (IP-NORMED-AG kqw_))
                           (VNB-LAMBDA kqk_ kqi_ ((ACT kqw_) ((IP kqv_) kqx_ (kqa_ kqk_)) (kqb_ kqk_)))
                           kqi_)))))))))))))

(def-functoid 'FINITE-RANK-OPS '(kqv_ kqw_)
  '(SEP kqt_ (BOUNDED-OPS kqv_ kqw_) (IS-FINITE-RANK-OP kqv_ kqw_ kqt_)))

;;; --------------------------------------------------------------------------------------------
;;; SELF-ADJOINT AND POSITIVE OPERATORS; EIGENSPACES; THE SQUARE ROOT AND |T|
(def-predicate 'IS-SELF-ADJOINT-OP '(kqv_ kqt_)
  '(AND (IN kqt_ (BOUNDED-OPS kqv_ kqv_))
        (FORALL kqx_ (IMPLIES (IN kqx_ (VEC kqv_))
          (FORALL kqy_ (IMPLIES (IN kqy_ (VEC kqv_))
            (= ((IP kqv_) (kqt_ kqx_) kqy_) ((IP kqv_) kqx_ (kqt_ kqy_)))))))))

(def-predicate 'IS-POSITIVE-OP '(kqv_ kqt_)
  '(AND (IS-SELF-ADJOINT-OP kqv_ kqt_)
        (FORALL kqx_ (IMPLIES (IN kqx_ (VEC kqv_))
          (AND (IN ((IP kqv_) (kqt_ kqx_) kqx_) RR)
               (<= 0 ((IP kqv_) (kqt_ kqx_) kqx_)))))))

;;; N_lambda(T) = ker(T - lambda I)
(def-functoid 'EIGENSPACE '(kqv_ kqt_ kqc_)
  '(SEP kqx_ (VEC kqv_) (= (kqt_ kqx_) ((ACT kqv_) kqc_ kqx_))))

(def-predicate 'IS-EIGENVALUE '(kqv_ kqt_ kqc_)
  '(AND (IN kqc_ CC)
        (FORSOME kqx_ (AND (IN kqx_ (EIGENSPACE kqv_ kqt_ kqc_))
                           (NOT (= kqx_ (VZERO kqv_)))))))

;;; the positive square root of T (s.3.2): the unique positive S with S S = T
(def-functoid 'OP-SQRT '(kqv_ kqt_)
  '(IOTA kqs_ (AND (IS-POSITIVE-OP kqv_ kqs_) (= (BOP-COMP kqv_ kqs_ kqs_) kqt_))))

;;; |T| = (T* T)^{1/2} (s.3.3)
(def-functoid 'ABS-OP '(kqv_ kqt_)
  '(OP-SQRT kqv_ (BOP-COMP kqv_ (OP-ADJOINT kqv_ kqv_ kqt_) kqt_)))

;;; --------------------------------------------------------------------------------------------
;;; ORTHONORMAL BASIS SETS AND THE CANONICAL ONE
(def-functoid 'ONB-SETS '(kqv_)
  '(SEP kqo_ (POWER (VEC kqv_)) (IS-ORTHONORMAL-BASIS kqv_ kqo_ (VNB-LAMBDA kqe_ kqo_ kqe_))))

(def-functoid 'CANON-ONB '(kqv_)
  '(CHOICE (ONB-SETS kqv_)))

;;; --------------------------------------------------------------------------------------------
;;; HILBERT-SCHMIDT (Def. 3.34, Prop. 3.37)
;;; sum_{i in ix} ||T e_i||^2, in [0, +inf]
(def-functoid 'HS-SUM '(kqv_ kqw_ kqi_ kqe_ kqt_)
  '(ESUM (VNB-LAMBDA kqk_ kqi_ (* (IP-NORM kqw_ (kqt_ (kqe_ kqk_))) (IP-NORM kqw_ (kqt_ (kqe_ kqk_)))))))

(def-predicate 'IS-HILBERT-SCHMIDT '(kqv_ kqw_ kqt_)
  '(AND (IN kqt_ (BOUNDED-OPS kqv_ kqw_))
        (FORSOME kqi_ (AND (IN kqi_ SET)
          (FORSOME kqe_ (AND (IN kqe_ (FUN kqi_ (VEC kqv_)))
            (AND (IS-ORTHONORMAL-BASIS kqv_ kqi_ kqe_)
                 (IN (HS-SUM kqv_ kqw_ kqi_ kqe_ kqt_) RR))))))))

;;; HS(v, w)
(def-functoid 'HS-OPS '(kqv_ kqw_)
  '(SEP kqt_ (BOUNDED-OPS kqv_ kqw_) (IS-HILBERT-SCHMIDT kqv_ kqw_ kqt_)))

;;; ||T||_HS = (sum ||T e||^2)^{1/2} over the canonical basis
(def-functoid 'HS-NORM '(kqv_ kqw_ kqt_)
  '(SQRT (HS-SUM kqv_ kqw_ (CANON-ONB kqv_) (VNB-LAMBDA kqe_ (CANON-ONB kqv_) kqe_) kqt_)))

;;; <S | T>_HS = sum <S e | T e> over the canonical basis (3.12)
(def-functoid 'HS-IP '(kqv_ kqw_ kqu_ kqt_)
  '(CC-FAMILY-SUM (VNB-LAMBDA kqe_ (CANON-ONB kqv_) ((IP kqw_) (kqu_ kqe_) (kqt_ kqe_)))))

;;; --------------------------------------------------------------------------------------------
;;; TRACE CLASS (Prop. 3.47 as the definition) AND THE TRACE (Def. 3.46)
(def-predicate 'IS-TRACE-CLASS '(kqv_ kqt_)
  '(AND (IN kqt_ (BOUNDED-OPS kqv_ kqv_))
        (FORSOME kqa_ (AND (IS-HILBERT-SCHMIDT kqv_ kqv_ kqa_)
          (FORSOME kqb_ (AND (IS-HILBERT-SCHMIDT kqv_ kqv_ kqb_)
                             (= kqt_ (BOP-COMP kqv_ kqa_ kqb_))))))))

(def-functoid 'TRACE-CLASS-OPS '(kqv_)
  '(SEP kqt_ (BOUNDED-OPS kqv_ kqv_) (IS-TRACE-CLASS kqv_ kqt_)))

;;; tr T = sum <T e | e> over the canonical basis
(def-functoid 'OP-TRACE '(kqv_ kqt_)
  '(CC-FAMILY-SUM (VNB-LAMBDA kqe_ (CANON-ONB kqv_) ((IP kqv_) (kqt_ kqe_) kqe_))))

;;; --------------------------------------------------------------------------------------------
;;; Notation
(notation! 'IS-COMPACT-OP 'kind 'predicate 'arity 3 'english "$3 is a compact operator from $1 to $2")
(notation! 'COMPACT-OPS 'kind 'functoid 'arity 2 'english "the compact operators from $1 to $2" 'tex "K({$1}, {$2})")
(notation! 'RANK-ONE-OP 'kind 'functoid 'arity 4 'english "the rank-one operator x |-> <x | $3> $4" 'tex "\\langle \\cdot \\mid {$3} \\rangle {$4}")
(notation! 'IS-FINITE-RANK-OP 'kind 'predicate 'arity 3 'english "$3 is a finite-rank operator from $1 to $2")
(notation! 'FINITE-RANK-OPS 'kind 'functoid 'arity 2 'english "the finite-rank operators from $1 to $2" 'tex "F({$1}, {$2})")
(notation! 'IS-SELF-ADJOINT-OP 'kind 'predicate 'arity 2 'english "$2 is a self-adjoint operator on $1")
(notation! 'IS-POSITIVE-OP 'kind 'predicate 'arity 2 'english "$2 is a positive operator on $1")
(notation! 'EIGENSPACE 'kind 'functoid 'arity 3 'english "the eigenspace of $2 for $3" 'tex "N_{$3}({$2})")
(notation! 'IS-EIGENVALUE 'kind 'predicate 'arity 3 'english "$3 is an eigenvalue of $2")
(notation! 'OP-SQRT 'kind 'functoid 'arity 2 'english "the positive square root of $2" 'tex "{$2}^{1/2}")
(notation! 'ABS-OP 'kind 'functoid 'arity 2 'english "the absolute value of $2" 'tex "\\lvert {$2} \\rvert")
(notation! 'ONB-SETS 'kind 'functoid 'arity 1 'english "the orthonormal basis sets of $1")
(notation! 'CANON-ONB 'kind 'functoid 'arity 1 'english "the chosen orthonormal basis of $1")
(notation! 'HS-SUM 'kind 'functoid 'arity 5 'english "the sum of ||$5 $4_i||^2 over $3" 'tex "\\sum_{i \\in {$3}} \\lVert {$5} {$4}_i \\rVert^2")
(notation! 'IS-HILBERT-SCHMIDT 'kind 'predicate 'arity 3 'english "$3 is a Hilbert-Schmidt operator from $1 to $2")
(notation! 'HS-OPS 'kind 'functoid 'arity 2 'english "the Hilbert-Schmidt operators from $1 to $2" 'tex "HS({$1}, {$2})")
(notation! 'HS-NORM 'kind 'functoid 'arity 3 'english "the Hilbert-Schmidt norm of $3" 'tex "\\lVert {$3} \\rVert_{HS}")
(notation! 'HS-IP 'kind 'functoid 'arity 4 'english "the Hilbert-Schmidt inner product of $3 and $4" 'tex "\\langle {$3} \\mid {$4} \\rangle_{HS}")
(notation! 'IS-TRACE-CLASS 'kind 'predicate 'arity 2 'english "$2 is a trace-class operator on $1")
(notation! 'TRACE-CLASS-OPS 'kind 'functoid 'arity 1 'english "the trace-class operators on $1" 'tex "T({$1})")
(notation! 'OP-TRACE 'kind 'functoid 'arity 2 'english "the trace of $2" 'tex "\\mathrm{tr}\\,{$2}")
