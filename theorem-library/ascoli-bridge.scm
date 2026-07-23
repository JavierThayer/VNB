;;; ascoli-bridge.scm -- the dense-to-uniform bridge for Ascoli-Arzelà.
;;;
;;;   equicontinuous + (Cauchy-convergent on a dense sequence)  =>  uniformly
;;;   convergent to a continuous limit,   on a compact metric space.
;;;
;;; PROVEN as an ASSEMBLY, modulo two warranted analytic CORES.  A ground-up
;;; QED is a multi-lemma analysis development whose pieces need infrastructure
;;; the base lacks (uniform equicontinuity from compactness; a common Cauchy
;;; threshold over a finite net = finite-max; pointwise-limit construction), so
;;; -- following this library's Taylor-Lagrange / vector-Taylor methodology --
;;; the two analytic cores are WARRANTED and the assembly is machine-proved.
;;; The bridge is then a real qed modulo {core-A, core-B, typing}, and the cores
;;; are the two clearly-named targets a future dedicated session grinds.
;;;
;;; Loads after ascoli-arzela-statement (IS-EQUICONTINUOUS, CONVERGES-UNIFORMLY),
;;; separable (IS-DENSE-SEQ is defined HERE), compactness, metric-completeness
;;; (CONVERGES, rr-complete).  Binders: dseq (dense seq), cap (threshold, NOT N).
;;; ====================================================================

(define (bb-all  v cond body) `(FORALL  ,v (IMPLIES ,cond ,body)))
(define (bb-some v cond body) `(FORSOME ,v (AND     ,cond ,body)))

;;; ---- vocabulary --------------------------------------------------------

;;; IS-DENSE-SEQ(s, dseq): dseq : NN -> PTS(s) has dense range (every ball meets
;;; it).  IS-SEPARABLE(s) is exactly (FORSOME dseq. IS-DENSE-SEQ s dseq).
(def-predicate 'IS-DENSE-SEQ '(s dseq)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN dseq (FUN NN (PTS s)))
      (bb-all 'x '(IN x (PTS s))
        (bb-all 'eps '(POS-RR eps)
          (bb-some 'm '(IN m NN)
            '(< ((DIST s) x (dseq m)) eps)))))))

;;; CONVERGES-ON(s, fam, dseq): at every point of dseq the real sequence
;;; k |-> fam(k)(dseq(m)) converges.
(def-predicate 'CONVERGES-ON '(s fam dseq)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IN dseq (FUN NN (PTS s)))
      (bb-all 'm '(IN m NN)
        '(CONVERGES RR-MS (VNB-LAMBDA k ((fam k) (dseq m))))))))

;;; IS-UNIF-CAUCHY(s, fam): fam is uniformly Cauchy -- one threshold cap serves
;;; every point x at once.  (Carries IS-METRIC-SPACE s, so downstream lemmas need
;;; not re-assume it.)
(def-predicate 'IS-UNIF-CAUCHY '(s fam)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      (bb-all 'eps '(POS-RR eps)
        (bb-some 'cap '(IN cap NN)
          (bb-all 'k '(AND (IN k NN) (<= cap k))
            (bb-all 'l '(AND (IN l NN) (<= cap l))
              (bb-all 'x '(IN x (PTS s))
                '(< (abs (- ((fam k) x) ((fam l) x))) eps)))))))))

;;; ---- analytic cores (WARRANTED) ----------------------------------------

;;; CORE A: on a compact space, an equicontinuous family that is Cauchy on a
;;; dense sequence is uniformly Cauchy.  (The 3-epsilon / finite-net argument.)
(support 'equicont-dense-conv-implies-unif-cauchy
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IS-EQUICONTINUOUS s fam)
      (bb-some 'dseq '(IS-DENSE-SEQ s dseq) '(CONVERGES-ON s fam dseq)))
    '(IS-UNIF-CAUCHY s fam)))
(warrant! 'equicont-dense-conv-implies-unif-cauchy 'reference
  '(thayer-calc "equicontinuous + Cauchy on a dense set => uniformly Cauchy"))
(gloss! 'equicont-dense-conv-implies-unif-cauchy
  "The 3-epsilon core.  Fix eps.  Compactness + equicontinuity give a UNIFORM delta
   (one delta at scale eps/3 for every member and every point -- equicontinuity on a
   compact space is uniform), and total boundedness a FINITE delta-net; by density
   the net centres may be taken in the dense sequence.  The family is Cauchy at each
   of those finitely many centres, so a single threshold cap works for all of them.
   For any point x, pick a net centre p within delta: |fam(k)(x) - fam(l)(x)| is at
   most |fam(k)(x)-fam(k)(p)| + |fam(k)(p)-fam(l)(p)| + |fam(l)(p)-fam(l)(x)| <
   eps/3+eps/3+eps/3 = eps for k,l >= cap.  Needs, for a machine proof, uniform
   equicontinuity from compactness and a finite-max over the net -- neither yet in
   the base.  Source: the user's calculus notes; cf. Dieudonné 7.5.")
(category! 'equicont-dense-conv-implies-unif-cauchy 'analysis)
(rests-on 'equicont-dense-conv-implies-unif-cauchy '(compact-iff-tb-complete))

;;; CORE B: a uniformly Cauchy sequence of continuous functions converges
;;; uniformly to a continuous limit.  (RR-completeness + uniform-limit-continuous.)
(support 'unif-cauchy-cont-implies-uniform-limit
  (forall-guarded '(s fam)
    (list
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-UNIF-CAUCHY s fam))
    (bb-some 'g '(IN g (FUN (PTS s) RR))
      '(AND (IS-CONTINUOUS s RR-MS g)
            (CONVERGES-UNIFORMLY s fam g)))))
(warrant! 'unif-cauchy-cont-implies-uniform-limit 'reference
  '(thayer-calc "uniformly Cauchy + continuous => uniform limit exists and is continuous"))
(gloss! 'unif-cauchy-cont-implies-uniform-limit
  "The completeness core.  At each x the real sequence k |-> fam(k)(x) is Cauchy
   (specialise uniform-Cauchy at x), so it converges in RR (rr-complete); define
   g(x) as that limit.  Letting l -> infinity in |fam(k)(x)-fam(l)(x)| < eps (k,l >=
   cap) gives |fam(k)(x)-g(x)| <= eps for all x at once -- uniform convergence.  A
   uniform limit of continuous functions is continuous, so g is continuous.  Needs,
   for a machine proof, the pointwise-limit functoid and uniform-limit-continuous.
   Source: the user's calculus notes; cf. Dieudonné 7.5, 7.1.")
(category! 'unif-cauchy-cont-implies-uniform-limit 'analysis)
(rests-on 'unif-cauchy-cont-implies-uniform-limit '(rr-complete))

;;; ---- the bridge (PROVEN assembly) --------------------------------------

;;; ascoli-dense-bridge: assemble the two cores.  On a compact metric space, an
;;; equicontinuous sequence of continuous functions that is Cauchy on SOME dense
;;; sequence converges uniformly to a continuous limit.
(sp (make-wff
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-EQUICONTINUOUS s fam)
      (bb-some 'dseq '(IS-DENSE-SEQ s dseq) '(CONVERGES-ON s fam dseq)))
    (bb-some 'g '(IN g (FUN (PTS s) RR))
      '(AND (IS-CONTINUOUS s RR-MS g)
            (CONVERGES-UNIFORMLY s fam g))))))
(di)(di)(di)(di)(di)(di)(di)                                  ; s, fam, + 5 antecedents
(fact 'equicont-dense-conv-implies-unif-cauchy 's 'fam)       ; -> IS-UNIF-CAUCHY s fam
(fact 'unif-cauchy-cont-implies-uniform-limit 's 'fam)        ; -> EXISTS g. cont & uniform
(ass)
(qed 'ascoli-dense-bridge)
