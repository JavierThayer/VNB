;;; frechet-banach-steinhaus.scm -- BOUNDED SETS and EQUICONTINUOUS FAMILIES of linear
;;; maps in a space with a countable family of seminorms (Thayer, "Analise Funcional e
;;; Teoria Espectral", Ch. 8 s.4, Def. 8.31 and the equicontinuity of Thm 8.32, p. 257).
;;; Added 2026-10-11 (batch TVS-2B).  Vocabulary only: the theorems (Banach-Steinhaus
;;; for Frechet spaces, and the closed graph theorem) are in
;;; theorem-library/frechet-banach-steinhaus.scm.
;;;
;;; THE MODEL.  As in frechet-open-mapping.scm, a seminormed space is a module m with a
;;; family fam : NN -> (VEC m -> RR) of seminorms, carried as an explicit parameter.
;;;
;;; DEF. 8.31 (bounded set).  A set A in a seminormed space (E, Gamma) is bounded when
;;; sup { p(f) : f in A } < infinity for every seminorm p in Gamma.  The supremum is
;;; written through an upper bound: for every k some real bd bounds fam(k) on A.
;;;
;;; EQUICONTINUITY (Thm 8.32, the book's seminorm form).  The book: {T_i} is
;;; equicontinuous when for every seminorm q in J there are p_1, ..., p_n in I and C
;;; with q(T_i x) <= C max{p_1(x), ..., p_n(x)} for all i and x.  With the domain family
;;; ENUMERATED, any finite set of seminorms lies in an INITIAL SEGMENT fam(0), ...,
;;; fam(nb) of it, and the maximum over a larger set is larger, so the initial segment
;;; suffices and is what is written.  The maximum is written through its upper bounds,
;;; as Prop. 8.26 is written in theorem-library/frechet-metric.scm (frm-bound-826):
;;; (fam1(j)(x) <= r for every j <= nb) => fam2(k)(T_i x) <= ck r.  This is that bound
;;; with ONE nb and ONE ck for the whole family: for a single map it is exactly the
;;; criterion `frm-cont-lin-iff-bound' proves equivalent to continuity.
;;;
;;; The family of maps is indexed by a class ix and given as tf : ix -> (VEC m1 -> VEC m2);
;;; the book's L(E, F) membership of each T_i (linearity and continuity) is a hypothesis
;;; of the theorem, not part of the predicate.
;;;
;;; Binders: aa the set, bd its bound, ix the index class, tf the family, nb the
;;; segment length, ck the constant.  Loads after frechet-open-mapping.
;;; ====================================================================

;;; IS-FR-BOUNDED(m, fam, aa): aa is a subset of VEC m on which every seminorm of the
;;; family is bounded above (Def. 8.31).
(def-predicate 'IS-FR-BOUNDED '(m fam aa)
  (conjuncts->and
    (list
      '(SUBSET aa (VEC m))
      (forall-guarded 'k '(IN k NN)
        (forsome-guarded 'bd '(IN bd RR)
          (forall-guarded 'y '(IN y aa) '(<= ((fam k) y) bd)))))))
(notation! 'IS-FR-BOUNDED 'kind 'predicate 'arity 3
           'english "$3 is a bounded set in ($1, $2)")
(def-comments! 'IS-FR-BOUNDED
  "$(m, \\mathit{fam})$ is the seminormed space ($m$ a module, $\\mathit{fam}(k)$ its $k$-th seminorm);"
  "$\\mathit{aa}$ is the set, a subset of $\\operatorname{vec}(m)$.")

;;; IS-FR-EQUICONT(m1, fam1, m2, fam2, ix, tf): the family tf(i), i in ix, of maps
;;; VEC m1 -> VEC m2 is equicontinuous in the seminorm form of Thm 8.32: for every k
;;; there are nb and ck > 0 with fam2(k)(tf(i)(x)) <= ck r whenever fam1(j)(x) <= r for
;;; all j <= nb, uniformly in i in ix and x in VEC m1.
(def-predicate 'IS-FR-EQUICONT '(m1 fam1 m2 fam2 ix tf)
  (conjuncts->and
    (list
      '(IN tf (FUN ix (FUN (VEC m1) (VEC m2))))
      (forall-guarded 'k '(IN k NN)
        (forsome-guarded 'nb '(IN nb NN)
          (forsome-guarded 'ck '(POS-RR ck)
            (forall-guarded 'i '(IN i ix)
              (forall-guarded 'x '(IN x (VEC m1))
                (forall-guarded 'r '(IN r RR)
                  '(IMPLIES (FORALL j (IMPLIES (IN j NN) (IMPLIES (<= j nb) (<= ((fam1 j) x) r))))
                            (<= ((fam2 k) ((tf i) x)) (* ck r))))))))))))
(notation! 'IS-FR-EQUICONT 'kind 'predicate 'arity 6
           'english "the family $6 indexed by $5 is equicontinuous from ($1, $2) to ($3, $4)")
(def-comments! 'IS-FR-EQUICONT
  "$(m_1, \\mathit{fam}_1)$ is the domain and $(m_2, \\mathit{fam}_2)$ the target, each a module with an $\\mathbb{N}$-enumerated seminorm family;"
  "$\\mathit{ix}$ is the index class and $\\mathit{tf}(i)$, for $i$ in $\\mathit{ix}$, the $i$-th map of the family.")
