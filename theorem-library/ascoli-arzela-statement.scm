;;; ascoli-arzela-statement.scm -- vocabulary + STATEMENT (no proof) of the
;;; Ascoli-Arzelà theorem, SEQUENTIAL form, RR-valued.  Warranted to the user's
;;; calculus notes (proof via Tychonoff for metric spaces); proof deferred.
;;; Added 2026-07-22 as a seed of the reference-warranted base.
;;;
;;; FORMULATION (user-confirmed): sequential.  A sequence of continuous
;;; RR-valued functions on a compact metric space that is EQUICONTINUOUS and
;;; POINTWISE-BOUNDED has a UNIFORMLY convergent subsequence.  This fits the
;;; library's countably-based / sequential-compactness grain and plugs straight
;;; into the existing diagonal engine.
;;;
;;; WHY THE EXISTING BASE ALMOST SUFFICES (the finding behind this seed):
;;;   * The hard core is present: coordinatewise-diagonal-subseq (a countable
;;;     product of seq-compact factors -- a sequence has a coordinatewise-
;;;     convergent subsequence) and compact-countable-product.  The Tychonoff
;;;     used is COUNTABLE, and that is ENOUGH: a compact metric space is
;;;     separable (compact => totally bounded => a countable dense set D), and an
;;;     equicontinuous family is pinned by its values on D, so the diagonal runs
;;;     over the COUNTABLE product Prod_{x in D}.  Countable Tychonoff is exactly
;;;     the right tool.
;;;   * Still MISSING (calculus-101 bridges, not deep machinery), to be added as
;;;     warranted supports before a machine proof:
;;;       (1) compact-metric-is-separable  (countable dense D; from totally-bounded)
;;;       (2) equicont + convergence-on-a-dense-set => uniform convergence
;;;     and the embedding of the sequence into Prod_{x in D} [-M_x, M_x].
;;;
;;; Case-fold-safe binders: fam = the family/sequence (NOT F -- folds onto f),
;;; del = the reindexer, cap = the uniform threshold (NOT N -- folds onto n),
;;; bd = a pointwise bound.  Loads after cauchy-subsequence (STRICTLY-MONO-NN,
;;; SUBSEQ), tychonoff-proof / seq-compact-product (the diagonal engine),
;;; metric-continuity (IS-CONTINUOUS), compactness (IS-COMPACT).
;;; ====================================================================

;;; Paren-safe quantifier builders (file-local, aa- prefix).  The definition
;;; bodies below are exactly the deep mixed-quantifier pyramids the formula-
;;; builders note warns NOT to hand-nest; each helper closes its own form, so
;;; balance is structural rather than eyeball-counted.
(define (aa-all  v cond body) `(FORALL  ,v (IMPLIES ,cond ,body)))   ; forall v. cond => body
(define (aa-some v cond body) `(FORSOME ,v (AND     ,cond ,body)))   ; exists v. cond & body

;;; ---- vocabulary --------------------------------------------------------

;;; IS-EQUICONTINUOUS(s, fam): the sequence fam : NN -> (PTS s -> RR) is
;;; equicontinuous -- for each point x and tolerance eps there is one delta that
;;; works for EVERY member fam(k) at once (delta depends on x, eps, NOT on k).
(def-predicate 'IS-EQUICONTINUOUS '(s fam)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      (aa-all 'x '(IN x (PTS s))
        (aa-all 'eps '(POS-RR eps)
          (aa-some 'del '(POS-RR del)
            (aa-all 'k '(IN k NN)
              (aa-all 'y '(IN y (PTS s))
                '(IMPLIES (< ((DIST s) x y) del)
                   (< (abs (- ((fam k) x) ((fam k) y))) eps))))))))))

;;; POINTWISE-BOUNDED(s, fam): at each point x the values { fam(k)(x) : k in NN }
;;; are bounded in RR (a bound bd that may depend on x).
(def-predicate 'POINTWISE-BOUNDED '(s fam)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      (aa-all 'x '(IN x (PTS s))
        (aa-some 'bd '(IN bd RR)
          (aa-all 'k '(IN k NN)
            '(<= (abs ((fam k) x)) bd)))))))

;;; CONVERGES-UNIFORMLY(s, seq, g): the sequence of functions seq : NN ->
;;; (PTS s -> RR) converges uniformly on PTS(s) to g -- one threshold cap works
;;; at every point x simultaneously.
(def-predicate 'CONVERGES-UNIFORMLY '(s seq g)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN seq (FUN NN (FUN (PTS s) RR)))
      '(IN g (FUN (PTS s) RR))
      (aa-all 'eps '(POS-RR eps)
        (aa-some 'cap '(IN cap NN)
          (aa-all 'k '(AND (IN k NN) (<= cap k))
            (aa-all 'x '(IN x (PTS s))
              '(< (abs (- ((seq k) x) (g x))) eps))))))))

;;; ---- the statement -----------------------------------------------------

;;; Ascoli-Arzelà (sequential, RR-valued).  On a compact metric space s, a
;;; sequence fam of continuous RR-valued functions that is equicontinuous and
;;; pointwise-bounded has a subsequence converging uniformly to a (necessarily
;;; continuous) limit g.
(support 'ascoli-arzela-sequential
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-EQUICONTINUOUS s fam)
      '(POINTWISE-BOUNDED s fam))
    (aa-some 'del '(STRICTLY-MONO-NN del)
      (aa-some 'g '(IN g (FUN (PTS s) RR))
        '(AND (IS-CONTINUOUS s RR-MS g)
              (CONVERGES-UNIFORMLY s (SUBSEQ fam del) g))))))

(warrant! 'ascoli-arzela-sequential 'reference
  '(thayer-calc "Ascoli-Arzelà, via Tychonoff for metric spaces"))

(gloss! 'ascoli-arzela-sequential
  "Ascoli-Arzelà, sequential form.  Let s be a compact metric space and fam : NN ->
   (PTS s -> RR) a sequence of continuous real-valued functions on s that is
   EQUICONTINUOUS (one delta per (x,eps) serves every fam(k)) and POINTWISE-BOUNDED
   (at each x the values fam(k)(x) are bounded).  Then fam has a subsequence
   fam o del (del strictly increasing) converging UNIFORMLY on s to a limit g, which
   is again continuous.  Classical source: Dieudonné, Foundations of Modern Analysis,
   Ascoli's theorem (§7.5).  Intended proof (the user's notes): s compact => totally
   bounded => a COUNTABLE dense set D; pointwise-boundedness puts each { fam(k)(x) } in
   a compact interval, so k |-> (fam(k)(x))_{x in D} is a sequence in the countable
   product Prod_{x in D} K_x; coordinatewise-diagonal-subseq extracts a subsequence
   convergent at every x in D; equicontinuity upgrades pointwise-convergence-on-D to
   uniform convergence on all of s.  STILL TO BUILD as warranted supports before a
   machine proof: compact-metric-is-separable (countable dense D) and the bridge
   'equicontinuous + convergent on a dense set => uniformly convergent'.")

(category! 'ascoli-arzela-sequential 'topology)

;; The route's declared dependencies: the Tychonoff/diagonal engine and the
;; separability bridge (compact => a countable dense set to diagonalise over).
;; Still missing, to be added when built: the dense-to-uniform bridge
;; (equicontinuous + convergent on a dense set => uniformly convergent).
(rests-on 'ascoli-arzela-sequential
  '(coordinatewise-diagonal-subseq compact-metric-is-separable ascoli-dense-bridge))
