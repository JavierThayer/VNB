;;; frechet-open-mapping.scm -- Frechet spaces, continuous linear maps, and the
;;; OPEN MAPPING (bounded-inverse form) and CLOSED GRAPH theorems (statement only).
;;; Seed for functional analysis.  Added 2026-07-22.
;;;
;;; The base has no topological vector space or locally-convex layer, so a
;;; Frechet space is modelled CONCRETELY (fits the library's countably-based
;;; grain): a module m over a normed field with a COUNTABLE SEPARATING SEMINORM
;;; FAMILY fam, sequentially complete w.r.t. that family.  Convergence,
;;; continuity and closed-graph are stated SEQUENTIALLY relative to the family
;;; (carried EXPLICITLY as a parameter -- the topology is family-independent,
;;; elided here).
;;;
;;; OPENNESS NEEDS NO TOPOLOGY LAYER.  For a LINEAR map, "open" is a statement
;;; about neighbourhoods of 0 alone: by translation invariance tt(x + V) =
;;; tt(x) + tt(V), so tt is open iff tt(V) is a neighbourhood of 0 for every
;;; neighbourhood V of 0.  And the countable family gives those neighbourhoods
;;; a canonical basic form -- FR-BALL(m, fam, n, eps) below, the finite prefix
;;; max_{k<=n} fam(k) < eps -- so the general open-mapping statement is directly
;;; expressible here (`open-mapping-theorem'), and no quantification over open
;;; sets occurs.  This is exactly the form the proof of Thm 4.7 of the user's
;;; TVS notes delivers: its last line is "tt(B_E(alpha)) contains B_F(s_1),
;;; whence tt(B_E(alpha)) is a neighbourhood of 0".  Schaefer III.1 (p. 74)
;;; makes the reduction the definition: a TOPOLOGICAL HOMOMORPHISM is a linear
;;; map open onto its image, and `open-mapping-theorem' below says exactly
;;; "tt is a topological homomorphism onto m2".  The bounded-inverse form is
;;; kept as the corollary it is.
;;;
;;; Note where the CLOSURE sits, since it is the whole difficulty: Cor. 4.6 of
;;; the notes gives only that CLOSURE(tt(V)) is a neighbourhood of 0 (Yosida
;;; II.5's Proposition, p. 75, is the same statement: V contained in (T U)^a),
;;; and it needs no completeness and no continuity.  Removing the bar is what
;;; the successive-approximation series in Thm 4.7 does, and that is where
;;; completeness of the DOMAIN is spent.  A statement of Cor. 4.6 would need
;;; CLOSURE for the seminorm family, which the base does not have (baire's
;;; CLOSURE is over a METRIC-SPACE); only the bar-free conclusion is stated.
;;;
;;; SCOPE.  The seminorm-family model is locally convex, so this is the Frechet
;;; case -- and "Frechet" does carry local convexity in current usage (Bourbaki,
;;; Schaefer, Treves), so the name here is right.  Yosida is the older usage and
;;; says so in as many words (Ch. I.9, p. 52, Remark): "The names F-space and
;;; B-space are abbreviations of Frechet space and Banach space... It is to be
;;; noted that BOURBAKI uses the term Frechet spaces for locally convex spaces
;;; which are quasi-normed and complete."  Yosida's F-space (Ch. I.9, Def. 1,
;;; p. 52) is a complete QUASI-NORMED linear space, and the open mapping theorem
;;; (Ch. II.5, p. 75) is stated for those -- no local convexity.
;;;
;;; Local convexity really is a restriction here: Example 1.11 of the notes
;;; (measurable functions mod null, metrized by integral |f-g|/(1+|f-g|)) is a
;;; complete metrizable TVS whose only convex neighbourhood of 0 is the whole
;;; space, hence carries no seminorm family at all.
;;;
;;; The F-space case is CLOSE, and it is a NORMED-AG away: Yosida's quasi-norm
;;; (Ch. I.2, Def. 2, p. 31) is ||x|| >= 0 with ||x|| = 0 iff x = 0, subadditive,
;;; and ||-x|| = ||x|| -- which is EXACTLY the `is-group-norm' property that
;;; normed-ag.scm already imposes -- plus two scalar-continuity clauses
;;; (||a.x_n|| -> 0 when ||x_n|| -> 0, and ||a_n.x|| -> 0 when a_n -> 0).  So an
;;; F-space is a module whose MODULE-VECTOR-AG is a NORMED-AG, plus those two
;;; clauses, plus IS-COMPLETE of NAG-METRIC-SPACE of it; and then BALL,
;;; IS-CONTINUOUS, IS-COMPLETE, IS-MEAGER / IS-NONMEAGER all apply as they
;;; stand -- including the non-meager-RANGE hypothesis that this file has to
;;; assume away.  See [[project_functional_analysis_seeds]].
;;;
;;; The genuinely general form is Schaefer IV.8 (p. 161): B-complete (Ptak)
;;; domain, barrelled codomain -- far outside this base.
;;;
;;; Likewise "closed mapping" means precisely "mapping with closed graph"
;;; (the closed-operator convention), which is what HAS-CLOSED-GRAPH says;
;;; between metrizable spaces the sequential form below IS closedness of the
;;; graph in the product.
;;;
;;; Loads after seminorm-hahn-banach (IS-SEMINORM) and baire-category.
;;; Binders: fam/fam1/fam2 families, tt/gg linear maps, seq sequences, lim limits.
;;; ====================================================================

;; x (-)_m y  in module m
(define (fr-sub m a b) `((VADD ,m) ,a ((VNEG ,m) ,b)))

;;; ---- seminorm family, sequential Cauchy / convergence ------------------

;;; IS-SEMINORM-FAMILY(m, fam): a countable family fam : NN -> (VEC m -> RR) of
;;; seminorms that SEPARATES points (only the zero vector has all fam(k) zero).
(def-predicate 'IS-SEMINORM-FAMILY '(m fam)
  (conjuncts->and
    (list
      '(IS-MODULE m)
      '(IS-NORMED-FIELD (SCAL m))
      '(IN fam (FUN NN (FUN (VEC m) RR)))
      (forall-guarded 'k '(IN k NN) '(IS-SEMINORM m (fam k)))
      (forall-guarded 'x '(IN x (VEC m))
        '(IMPLIES (NOT (= x (VZERO m)))
           (FORSOME k (AND (IN k NN) (NOT (= ((fam k) x) 0)))))))))
(notation! 'IS-SEMINORM-FAMILY 'kind 'predicate 'arity 2
           'english "$2 is a separating countable family of seminorms on $1")

;;; FR-CONV(m, fam, seq, lim): seq -> lim in every seminorm of the family.
(def-predicate 'FR-CONV '(m fam seq lim)
  (forall-guarded 'k '(IN k NN)
    (forall-guarded 'eps '(POS-RR eps)
      (forsome-guarded 'cap '(IN cap NN)
        (forall-guarded 'i '(AND (IN i NN) (<= cap i))
          `(< ((fam k) ,(fr-sub 'm '(seq i) 'lim)) eps))))))
(notation! 'FR-CONV 'kind 'predicate 'arity 4
           'english "$3 converges to $4 in ($1, $2)")

;;; FR-CAUCHY(m, fam, seq): seq is Cauchy in every seminorm of the family.
(def-predicate 'FR-CAUCHY '(m fam seq)
  (forall-guarded 'k '(IN k NN)
    (forall-guarded 'eps '(POS-RR eps)
      (forsome-guarded 'cap '(IN cap NN)
        (forall-guarded 'i '(AND (IN i NN) (<= cap i))
          (forall-guarded 'j '(AND (IN j NN) (<= cap j))
            `(< ((fam k) ,(fr-sub 'm '(seq i) '(seq j))) eps)))))))
(notation! 'FR-CAUCHY 'kind 'predicate 'arity 3
           'english "$3 is Cauchy in ($1, $2)")

;;; ---- Frechet space (concrete: family + sequential completeness) --------

;;; IS-FRECHET-STRUCTURE(m, fam): m with the separating seminorm family fam is a
;;; Frechet space -- every fam-Cauchy sequence fam-converges to a point of m.
(def-predicate 'IS-FRECHET-STRUCTURE '(m fam)
  (conjuncts->and
    (list
      '(IS-SEMINORM-FAMILY m fam)
      (forall-guarded 'seq '(IN seq (FUN NN (VEC m)))
        '(IMPLIES (FR-CAUCHY m fam seq)
           (FORSOME lim (AND (IN lim (VEC m)) (FR-CONV m fam seq lim))))))))
(notation! 'IS-FRECHET-STRUCTURE 'kind 'predicate 'arity 2
           'english "($1, $2) is a Frechet space")

;;; ---- linear and continuous-linear maps ---------------------------------

;;; IS-LINEAR-MAP(m1, m2, tt): tt : VEC(m1) -> VEC(m2) additive and homogeneous
;;; over a common scalar field.
(def-predicate 'IS-LINEAR-MAP '(m1 m2 tt)
  (conjuncts->and
    (list
      '(IS-MODULE m1)
      '(IS-MODULE m2)
      '(= (SCAL m1) (SCAL m2))
      '(IN tt (FUN (VEC m1) (VEC m2)))
      (forall-guarded 'x '(IN x (VEC m1))
        (forall-guarded 'y '(IN y (VEC m1))
          '(= (tt ((VADD m1) x y)) ((VADD m2) (tt x) (tt y)))))
      (forall-guarded 'lam '(IN lam (CARR (SCAL m1)))
        (forall-guarded 'x '(IN x (VEC m1))
          '(= (tt ((ACT m1) lam x)) ((ACT m2) lam (tt x))))))))
(notation! 'IS-LINEAR-MAP 'kind 'predicate 'arity 3
           'english "$3 is a linear map from $1 to $2")

;;; IS-CONT-LIN(m1, fam1, m2, fam2, tt): tt is linear and sequentially continuous
;;; (fam1-convergent sequences map to fam2-convergent sequences, to the image).
(def-predicate 'IS-CONT-LIN '(m1 fam1 m2 fam2 tt)
  (conjuncts->and
    (list
      '(IS-LINEAR-MAP m1 m2 tt)
      (forall-guarded 'seq '(IN seq (FUN NN (VEC m1)))
        (forall-guarded 'lim '(IN lim (VEC m1))
          '(IMPLIES (FR-CONV m1 fam1 seq lim)
             (FR-CONV m2 fam2 (VNB-LAMBDA i NN (tt (seq i))) (tt lim))))))))
(notation! 'IS-CONT-LIN 'kind 'predicate 'arity 5
           'english "$5 is a continuous linear map from ($1, $2) to ($3, $4)")

;;; HAS-CLOSED-GRAPH(m1, fam1, m2, fam2, tt): whenever seq -> p1 and tt(seq) -> p2,
;;; the limit is consistent (p2 = tt(p1)).
(def-predicate 'HAS-CLOSED-GRAPH '(m1 fam1 m2 fam2 tt)
  (conjuncts->and
    (list
      '(IS-LINEAR-MAP m1 m2 tt)
      (forall-guarded 'seq '(IN seq (FUN NN (VEC m1)))
        (forall-guarded 'p1 '(IN p1 (VEC m1))
          (forall-guarded 'p2 '(IN p2 (VEC m2))
            '(IMPLIES (AND (FR-CONV m1 fam1 seq p1)
                           (FR-CONV m2 fam2 (VNB-LAMBDA i NN (tt (seq i))) p2))
               (= p2 (tt p1)))))))))
(notation! 'HAS-CLOSED-GRAPH 'kind 'predicate 'arity 5
           'english "$5 has a closed graph from ($1, $2) to ($3, $4)")

;;; ---- basic neighbourhoods of 0, and openness of a linear map -----------

;;; FR-BALL(m, fam, n, eps) = { x in VEC m : fam(k)(x) < eps for all k <= n },
;;; the basic neighbourhood of 0 cut out by the finite prefix fam(0..n) of the
;;; family.  Prefixes are cofinal among finite subfamilies, so these are a
;;; fundamental system of neighbourhoods of 0 for the family topology.
(def-functoid 'FR-BALL '(m fam n eps)
  '(SEP x (VEC m)
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n)) (< ((fam k) x) eps)))))

;;; IS-OPEN-LIN-MAP(m1, fam1, m2, fam2, tt): tt is linear and the image of every
;;; basic neighbourhood of 0 is a neighbourhood of 0.  For a linear map this is
;;; openness outright -- tt(x + V) = tt(x) + tt(V).
(def-predicate 'IS-OPEN-LIN-MAP '(m1 fam1 m2 fam2 tt)
  (conjuncts->and
    (list
      '(IS-LINEAR-MAP m1 m2 tt)
      (forall-guarded 'n '(IN n NN)
        (forall-guarded 'eps '(POS-RR eps)
          (forsome-guarded 'n_ '(IN n_ NN)
            (forsome-guarded 'eps_ '(POS-RR eps_)
              '(SUBSET (FR-BALL m2 fam2 n_ eps_)
                       (IMAGE tt (FR-BALL m1 fam1 n eps))))))))))
(notation! 'IS-OPEN-LIN-MAP 'kind 'predicate 'arity 5
           'english "$5 is an open linear map from ($1, $2) to ($3, $4)")

;;; ---- the theorems ------------------------------------------------------

;;; CLOSED GRAPH THEOREM: a linear map between Frechet spaces with closed graph is
;;; continuous.
(support 'closed-graph-theorem
  (forall-guarded '(m1 fam1 m2 fam2 tt)
    (list
      '(IS-FRECHET-STRUCTURE m1 fam1)
      '(IS-FRECHET-STRUCTURE m2 fam2)
      '(HAS-CLOSED-GRAPH m1 fam1 m2 fam2 tt))
    '(IS-CONT-LIN m1 fam1 m2 fam2 tt)))
(warrant! 'closed-graph-theorem 'reference '(thayer-tvs "Theorem 4.9" 43))
(gloss! 'closed-graph-theorem
  "Closed graph theorem: a CLOSED linear map tt between Frechet spaces -- closed
   meaning precisely that its graph is closed, i.e. seq -> p1 and tt(seq) -> p2
   force p2 = tt(p1) -- is continuous.  A corollary of the open mapping theorem:
   the graph G is a closed subspace of the product, projG->E is a continuous linear
   bijection, so its inverse is continuous and tt = projG->F o (projG->E)^-1.
   Sources: the user's TVS notes Thm 4.9; Yosida II.6.  Uses Baire.")
(category! 'closed-graph-theorem 'analysis)
(rests-on 'closed-graph-theorem '(open-mapping-theorem))

;;; OPEN MAPPING THEOREM: a continuous linear SURJECTION between Frechet spaces
;;; is open -- the image of each basic neighbourhood of 0 contains one.
(support 'open-mapping-theorem
  (forall-guarded '(m1 fam1 m2 fam2 tt)
    (list
      '(IS-FRECHET-STRUCTURE m1 fam1)
      '(IS-FRECHET-STRUCTURE m2 fam2)
      '(IS-CONT-LIN m1 fam1 m2 fam2 tt)
      '(FORALL y (IMPLIES (IN y (VEC m2))
           (FORSOME x (AND (IN x (VEC m1)) (= y (tt x)))))))
    '(IS-OPEN-LIN-MAP m1 fam1 m2 fam2 tt)))
(warrant! 'open-mapping-theorem 'reference '(thayer-tvs "Theorem 4.7" 42))
(gloss! 'open-mapping-theorem
  "Open mapping theorem (Banach): a continuous linear surjection tt between Frechet
   spaces is open.  Stated where openness of a LINEAR map actually lives -- at 0:
   the image of the basic neighbourhood FR-BALL(m1, fam1, n, eps) contains a basic
   neighbourhood FR-BALL(m2, fam2, n', eps').  No open-set quantification is needed
   and none occurs in the proof.  In Schaefer's vocabulary (III.1, p. 74) this says
   tt is a TOPOLOGICAL HOMOMORPHISM onto m2.  Sources: the user's TVS notes Thm 4.7;
   Schaefer III.2 (Banach's homomorphism theorem, p. 76); Yosida II.5 (p. 75, for
   F-spaces, i.e. without local convexity).  Those three prove more than is stated
   here: the codomain need only be a Hausdorff TVS and tt's RANGE need only be
   non-meager, whence tt is surjective and the codomain complete metrizable.  Here
   surjectivity is assumed and the codomain is assumed Frechet -- meagerness
   relative to a seminorm family is not in the base.  Uses Baire.")
(category! 'open-mapping-theorem 'analysis)
(rests-on 'open-mapping-theorem '(baire-category))

;;; OPEN MAPPING THEOREM (bounded-inverse form): a continuous linear bijection
;;; between Frechet spaces has a continuous inverse.  (gg is a linear two-sided
;;; inverse of the continuous linear tt; conclude gg is continuous.)
(support 'open-mapping-bounded-inverse
  (forall-guarded '(m1 fam1 m2 fam2 tt gg)
    (list
      '(IS-FRECHET-STRUCTURE m1 fam1)
      '(IS-FRECHET-STRUCTURE m2 fam2)
      '(IS-CONT-LIN m1 fam1 m2 fam2 tt)
      '(IS-LINEAR-MAP m2 m1 gg)
      '(FORALL x (IMPLIES (IN x (VEC m1)) (= (gg (tt x)) x)))
      '(FORALL y (IMPLIES (IN y (VEC m2)) (= (tt (gg y)) y))))
    '(IS-CONT-LIN m2 fam2 m1 fam1 gg)))
(warrant! 'open-mapping-bounded-inverse 'reference
  '(yosida "Corollary of the open mapping theorem, Ch. II.6" 94))
(gloss! 'open-mapping-bounded-inverse
  "Open mapping theorem, bounded-inverse form: a continuous linear bijection tt
   between Frechet spaces (with linear two-sided inverse gg) has continuous inverse
   gg.  A corollary of `open-mapping-theorem': openness of tt is continuity of gg.
   Sources: Yosida II.5; the user's TVS notes, Thm 4.7.  Uses Baire.")
(category! 'open-mapping-bounded-inverse 'analysis)
(rests-on 'open-mapping-bounded-inverse '(open-mapping-theorem))
