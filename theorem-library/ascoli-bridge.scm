;;; ascoli-bridge.scm -- the dense-to-uniform bridge for Ascoli-Arzelà.
;;;
;;;   equicontinuous + (Cauchy-convergent on a dense sequence)  =>  uniformly
;;;   convergent to a continuous limit,   on a compact metric space.
;;;
;;; PROVEN as an ASSEMBLY.  It rested on two warranted analytic CORES; CORE A
;;; is PROVEN (theorem-library/ascoli-analytic-cores.scm, 2026-08-23) down to a
;;; single asserted compactness rung, and CORE B -- the pointwise-limit
;;; construction plus "a uniform limit of continuous maps is continuous" --
;;; is PROVEN in two halves: the construction in
;;; theorem-library/unif-cauchy-limit.scm (2026-09-14) and the continuity in
;;; ascoli-analytic-cores.scm.  Nothing is asserted in this file any more.
;;;
;;; Loads after ascoli-analytic-cores (IS-DENSE-SEQ, CONVERGES-ON, IS-UNIF-CAUCHY
;;; are defined THERE, and CORE A is proved there), unif-cauchy-limit
;;; (unif-cauchy-has-uniform-limit, immediately above), ascoli-arzela-statement
;;; (IS-EQUICONTINUOUS, CONVERGES-UNIFORMLY), separable, compactness,
;;; metric-completeness (CONVERGES, rr-complete).
;;; Binders: dseq (dense sequence), cap (threshold, NOT N).
;;; ====================================================================

;;; ---- vocabulary: MOVED ------------------------------------------------
;;; IS-DENSE-SEQ, CONVERGES-ON and IS-UNIF-CAUCHY were defined here until
;;; 2026-08-23; they now live in theorem-library/ascoli-analytic-cores.scm, which
;;; loads immediately before this file and needs them for its proofs.

;;; ---- CORE A: PROVEN, and no longer here --------------------------------
;;; `equicont-dense-conv-implies-unif-cauchy' was an asserted `reference'
;;; support in this file, glossed as "the 3-epsilon core".  It is PROVEN in
;;; ascoli-analytic-cores.scm, as the composition of
;;;   equicont-dense-conv-ptwise-cauchy       (proved, modulo 0, no compactness)
;;; with
;;;   ptwise-cauchy-compact-equicont-unif     (asserted: finite subcover + max).
;;; The split follows the user's notes, which state the two as Lemma 3.36 and
;;; Prop 3.33 and use compactness only in the second.

;;; ---- CORE B, split the same way -----------------------------------------
;;;
;;; CORE B was one assertion: "a uniformly Cauchy sequence of CONTINUOUS maps
;;; converges uniformly to a CONTINUOUS limit".  Two things are bundled there,
;;; and only the first needs machinery the base lacks:
;;;
;;;   (B1) the limit EXISTS, and the convergence is uniform.  A construction:
;;;        g(x) is the limit of the Cauchy real sequence k |-> fam(k)(x), and
;;;        the uniform estimate comes from passing to the limit in
;;;        |fam(k)(x) - fam(l)(x)| < eps.  PROVEN -- `unif-cauchy-has-uniform-limit',
;;;        theorem-library/unif-cauchy-limit.scm (2026-09-14): g is
;;;        VNB-LAMBDA x in PTS(s). SEQ-LIMIT(VNB-LAMBDA k in NN. fam(k)(x)),
;;;        with seq-limit-core's rr-cauchy-converges, seq-limit-converges-to
;;;        and rr-limit-tail-abs-le doing exactly the two things the retired
;;;        gloss said the tree lacked.
;;;   (B2) the limit is CONTINUOUS.  PROVEN -- `uniform-limit-continuous',
;;;        theorem-library/ascoli-analytic-cores.scm.  No construction, no
;;;        completeness: a 3-epsilon argument about a limit already given.
;;;
;;; Note that B1 does not mention continuity at all: it is the completeness of
;;; the uniform metric, and the continuity hypothesis of CORE B is spent only in
;;; B2.  Splitting them made that visible.

;;; B1 -- the construction.  The `support' of unif-cauchy-has-uniform-limit,
;;; with its `reference' warrant, gloss, topic and rests-on, stood here until
;;; 2026-09-14; RETIRED, the theorem being proven in
;;; theorem-library/unif-cauchy-limit.scm, which loads just before this file.

;;; CORE B -- now an ASSEMBLY of B1 and B2.
(sp (make-wff
  (forall-guarded '(s fam)
    (list
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-UNIF-CAUCHY s fam))
    (forsome-guarded 'g '(IN g (FUN (PTS s) RR))
      '(AND (IS-CONTINUOUS s RR-MS g)
            (CONVERGES-UNIFORMLY s fam g))))))
(define (acb-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1))) n))))
(acb-peel!)
;;; B1 delivers the limit; skolemize it, name it, and B2 makes it continuous.
(let* ((ex  (dk-fact! 'unif-cauchy-has-uniform-limit 's 'fam))
       (new (car (dk-landed* (lambda () (ai ex)))))
       (gg  (car (filter (lambda (v) (not (memq v (free-vars ex))))
                         (free-vars new)))))
  (dk-split! new)
  (fact 'uniform-limit-continuous 's 'fam gg)
  (ew gg)
  (prop))
(qed 'unif-cauchy-cont-implies-uniform-limit)
(topic! 'unif-cauchy-cont-implies-uniform-limit 'analysis)
(gloss! 'unif-cauchy-cont-implies-uniform-limit
  "The completeness core.  Was an asserted `reference' support; it is now the
   composition of `unif-cauchy-has-uniform-limit' (the construction, PROVEN
   2026-09-14 in unif-cauchy-limit.scm) with `uniform-limit-continuous'
   (PROVEN).")

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
      '(IS-EQUICONTINUOUS s RR-MS fam)
      (forsome-guarded 'dseq '(IS-DENSE-SEQ s dseq) '(CONVERGES-ON s fam dseq)))
    (forsome-guarded 'g '(IN g (FUN (PTS s) RR))
      '(AND (IS-CONTINUOUS s RR-MS g)
            (CONVERGES-UNIFORMLY s fam g))))))
(di)(di)(di)(di)(di)(di)(di)                                  ; s, fam, + 5 antecedents
(fact 'equicont-dense-conv-implies-unif-cauchy 's 'fam)       ; -> IS-UNIF-CAUCHY s fam
(fact 'unif-cauchy-cont-implies-uniform-limit 's 'fam)        ; -> EXISTS g. cont & uniform
(ass)
(qed 'ascoli-dense-bridge)
