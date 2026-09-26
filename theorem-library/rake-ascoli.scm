;;; theorem-library/rake-ascoli.scm
;;; ====================================================================
;;; Ascoli-Arzela (sequential, RR-valued) -- batch 8-B.
;;;
;;; `ascoli-arzela-sequential' (theorem-library/ascoli-arzela-statement.scm:114)
;;; is NOT proven here, and the head comment of this file says exactly why and
;;; what is left.  What IS proven here, modulo 0:
;;;
;;;   equicont-subseq                 a subsequence of an equicontinuous family
;;;                                   is equicontinuous
;;;   ascoli-sequential-from-diagonal the WHOLE of Ascoli-Arzela except the
;;;                                   pointwise diagonal extraction, which is
;;;                                   taken as one named antecedent
;;;
;;; THE STATE OF THE ROUTE.  Every rung of the intended proof is a theorem
;;; except one:
;;;   compact-metric-is-separable         PROVEN (compact-separable-proof.scm)
;;;   ascoli-dense-bridge                 PROVEN (ascoli-bridge.scm)
;;;   equicont-dense-conv-implies-unif-cauchy  PROVEN (ascoli-assembly.scm)
;;;   coordinatewise-diagonal-subseq      PROVEN (rake-diagonal-subseq.scm)
;;;   convergence-block-tower             PROVEN (rake-block-tower.scm)
;;; and the missing one is the EMBEDDING of the family into a countable product
;;; of factors that the diagonal can consume.  coordinatewise-diagonal-subseq
;;; demands IS-MS-SEQUENCE(ms) with every (ms n) SEQ-COMPACT; the factors Ascoli
;;; needs are the closed bounded intervals [-M_x, M_x], and the tree has no
;;; metric SUBSPACE structure, so they are not metric spaces at all -- the wall
;;; the brief names, and the one heine-borel-baby.scm, monotone-inverse.scm and
;;; ascoli-arzela-statement.scm:155 each record.
;;;
;;; THE WAY ROUND that was tried and what it costs is written up in the report
;;; and in the closing block of this file: a POINTWISE Bolzano-Weierstrass run
;;; through the block-tower mechanism needs ONE analytic brick that the tree
;;; does not have (`bounded real sequence + infinite index block => it converges
;;; along an infinite sub-block'), plus a re-run of rake-block-tower's part B
;;; with that brick in place of SEQ-COMPACT.  Neither is cheap, so this file
;;; stops at the reduction and states the obligation exactly.
;;;
;;; WHAT THE REDUCTION BUYS.  `ascoli-sequential-from-diagonal' has Ascoli's own
;;; hypotheses, plus the inhabitedness guard that compact-metric-is-separable
;;; carries (the empty metric space: PTS(s) = {} is vacuously compact and
;;; FUN(NN, {}) is empty, so no dense SEQUENCE exists -- the defect recorded in
;;; structure-library/separable.scm), plus ONE antecedent:
;;;
;;;   forall dseq.  IS-DENSE-SEQ(s, dseq)
;;;     =>  forsome del.  STRICTLY-MONO-NN(del) and CONVERGES-ON(s, SUBSEQ(fam, del), dseq)
;;;
;;; and concludes Ascoli's conclusion verbatim.  So the whole remaining content
;;; of Ascoli-Arzela is that antecedent, with the hypotheses of Ascoli
;;; (POINTWISE-BOUNDED is what pays for it, and it is used nowhere else).
;;;
;;; LOAD WINDOW [hi is the end of load.scm].
;;;   lo: the latest citations are `subseq-apply' (theorem-library/rake-diagonal-
;;;   subseq) and `compact-metric-is-separable' (theorem-library/compact-
;;;   separable-proof); the others are ascoli-dense-bridge (ascoli-bridge),
;;;   fun-apply-type-c (fun-apply-type-proof) and the definitions
;;;   IS-EQUICONTINUOUS / CONVERGES-ON / IS-DENSE-SEQ / IS-SEPARABLE.
;;;   hi: nothing cites either new theorem; ascoli-arzela-sequential itself is
;;;   named only in metadata files (pss-topics, reference-topics).
;;;   So: immediately AFTER theorem-library/rake-diagonal-subseq.
;;;
;;; Helper prefix: r9b-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r9b-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-ascoli: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-ascoli: unfinished" name))))

;; The FUN NN NN typing carried by STRICTLY-MONO-NN, landed without consuming
;; the predicate (mac-h REPLACES what it unfolds, and the predicate is wanted
;; again by every later citation).
(define (r9b-fun-typing! ps)
  (have! (list 'IN ps '(FUN NN NN))
    (lambda ()
      (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN ps))
      (dk-split-all!)
      (ass))))

;; The conjunct list of a def-predicate hypothesis, unfolded DESTRUCTIVELY.
(define (r9b-unfold! name form)
  (dk-split-all! (dk-landed (lambda () (mac-h name form)))))

(define (r9b-need pred what lst)
  (or (any-pred pred lst) (error "rake-ascoli: missing" what)))

;;; =====================================================================
;;; L1.  equicont-subseq -- equicontinuity passes to a subsequence.
;;;
;;;   IS-EQUICONTINUOUS(s, t, fam),  STRICTLY-MONO-NN(phi)
;;;     =>  IS-EQUICONTINUOUS(s, t, SUBSEQ(fam, phi))
;;;
;;; The delta that serves every member of fam serves every member of the
;;; subsequence, because each member of the subsequence IS a member of fam.
;;; The only mechanics are the value equation `subseq-apply' at a TYPED index
;;; (never `mac SUBSEQ' under the binder: that owes the unprovable (IN (phi k) NN)
;;; in the outer context) and the FUN typing of the reindexed family.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (FORALL t
       (FORALL fam
         (FORALL phi
           (IMPLIES (IS-EQUICONTINUOUS s t fam)
             (IMPLIES (STRICTLY-MONO-NN phi)
               (IS-EQUICONTINUOUS s t (SUBSEQ fam phi))))))))))

(define r9b-e-landed (dk-peel!))

(define r9b-e-H (dk-pick (dk-head? 'IS-EQUICONTINUOUS) "the equicontinuity hypothesis"))
(define r9b-e-s   (cadr r9b-e-H))
(define r9b-e-t   (caddr r9b-e-H))
(define r9b-e-fam (cadddr r9b-e-H))
(define r9b-e-phi
  (cadr (dk-pick (dk-head? 'STRICTLY-MONO-NN) "the reindexer")))
(define r9b-e-cod (list 'FUN (list 'PTS r9b-e-s) (list 'PTS r9b-e-t)))

(r9b-fun-typing! r9b-e-phi)

(define r9b-e-atoms (r9b-unfold! 'IS-EQUICONTINUOUS r9b-e-H))
(define r9b-e-U
  (r9b-need (dk-head? 'FORALL) "the equicontinuity clause" r9b-e-atoms))

;; the reindexed family is again a sequence of maps
(define (r9b-e-typing!)
  (mac 'SUBSEQ)
  (dk-lam-t!)
  (let ((kv (dk-di-var!)))
    (fact 'fun-apply-type-c r9b-e-phi 'NN 'NN kv)
    (fact 'fun-apply-type-c r9b-e-fam 'NN r9b-e-cod (list r9b-e-phi kv))
    (ass)))

;; the (x, eps) lane: the SAME delta the hypothesis gives
(define (r9b-e-main!)
  (let* ((landed (dk-peel!))
         (ev (cadr (r9b-need (dk-head? 'POS-RR) "eps" landed)))
         (xv (cadr (r9b-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                              (equal? (caddr f) (list 'PTS r9b-e-s))))
                             "the point x" landed)))
         (ex (dk-apply! r9b-e-U xv ev))
         (dv (dk-skolem! ex))
         (hin (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (dk-contains? f dv)))
                       "the uniform-in-k clause")))
    (witness! dv
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'POS-RR)
               (ass)
               (let* ((l2 (dk-peel!))
                      (kv (cadr (r9b-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                           (eq? (caddr f) 'NN)))
                                          "the index k" l2)))
                      (yv (cadr (r9b-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                           (equal? (caddr f)
                                                                   (list 'PTS r9b-e-s))))
                                          "the second point y" l2))))
                 (fact 'fun-apply-type-c r9b-e-phi 'NN 'NN kv)
                 (subst (dk-fact! 'subseq-apply r9b-e-fam r9b-e-phi kv))
                 (dk-apply! hin (list r9b-e-phi kv) yv)
                 (ass)))))))))

(mac 'IS-EQUICONTINUOUS)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IN) (r9b-e-typing!))
           ((eq? (car g) 'FORALL) (r9b-e-main!))
           (#t (ass))))))

(r9b-qed! 'equicont-subseq)
(topic! 'equicont-subseq 'analysis)
(gloss! 'equicont-subseq
  "Equicontinuity passes to a subsequence: if one delta serves every member of
   fam at (x, eps), it serves every member of SUBSEQ(fam, phi), each of which is
   a member of fam.")

;;; =====================================================================
;;; L2.  ascoli-sequential-from-diagonal -- Ascoli-Arzela, modulo the
;;; pointwise diagonal extraction.
;;;
;;; The conclusion and the first five antecedents are copied from
;;; `ascoli-arzela-sequential' (ascoli-arzela-statement.scm:114).  The two added
;;; antecedents are the inhabitedness guard, spelled exactly as
;;; compact-metric-is-separable spells it, and the diagonal.
;;; =====================================================================

(define r9b-a-stmt
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(FORSOME x (IN x (PTS s)))
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-EQUICONTINUOUS s RR-MS fam)
      '(POINTWISE-BOUNDED s fam)
      '(FORALL dseq
         (IMPLIES (IS-DENSE-SEQ s dseq)
           (FORSOME del
             (AND (STRICTLY-MONO-NN del)
                  (CONVERGES-ON s (SUBSEQ fam del) dseq))))))
    (forsome-guarded 'del '(STRICTLY-MONO-NN del)
      (forsome-guarded 'g '(IN g (FUN (PTS s) RR))
        '(AND (IS-CONTINUOUS s RR-MS g)
              (CONVERGES-UNIFORMLY s (SUBSEQ fam del) g))))))

(sp (make-wff r9b-a-stmt))

(define r9b-a-landed (dk-peel!))

(define r9b-a-s (cadr (dk-pick (dk-head? 'IS-COMPACT) "the compact space")))
(define r9b-a-cod (list 'FUN (list 'PTS r9b-a-s) 'RR))
(define r9b-a-fam
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) (list 'FUN 'NN r9b-a-cod))))
                 "the family")))
(define r9b-a-HCONT
  (r9b-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (dk-contains? f 'IS-CONTINUOUS)))
            "the memberwise continuity" r9b-a-landed))
(define r9b-a-HDIAG
  (r9b-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (dk-contains? f 'IS-DENSE-SEQ)))
            "the diagonal hypothesis" r9b-a-landed))

;;; ---- a countable dense sequence ---------------------------------------

(define r9b-a-SEP (dk-fact! 'compact-metric-is-separable r9b-a-s))
(define r9b-a-sep-atoms (r9b-unfold! 'IS-SEPARABLE r9b-a-SEP))
(define r9b-a-EXD
  (r9b-need (dk-head? 'FORSOME) "the dense sequence" r9b-a-sep-atoms))
(define r9b-a-dseq (dk-skolem! r9b-a-EXD))

(have! (list 'IS-DENSE-SEQ r9b-a-s r9b-a-dseq)
  (lambda () (mac 'IS-DENSE-SEQ) (dk-conj-close! (lambda () (ass)))))

;;; ---- the diagonal subsequence -----------------------------------------

(define r9b-a-EXDEL (dk-apply! r9b-a-HDIAG r9b-a-dseq))
(define r9b-a-del (dk-skolem! r9b-a-EXDEL))
(define r9b-a-sub (list 'SUBSEQ r9b-a-fam r9b-a-del))

(r9b-fun-typing! r9b-a-del)

(have! (list 'IN r9b-a-sub (list 'FUN 'NN r9b-a-cod))
  (lambda ()
    (mac 'SUBSEQ)
    (dk-lam-t!)
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r9b-a-del 'NN 'NN kv)
      (fact 'fun-apply-type-c r9b-a-fam 'NN r9b-a-cod (list r9b-a-del kv))
      (ass))))

;; every member of the subsequence is a member of the family, hence continuous
(have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
               (list 'IS-CONTINUOUS r9b-a-s 'RR-MS (list r9b-a-sub 'k))))
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r9b-a-del 'NN 'NN kv)
      (subst (dk-fact! 'subseq-apply r9b-a-fam r9b-a-del kv))
      (dk-apply! r9b-a-HCONT (list r9b-a-del kv))
      (ass))))

(have! (list 'IS-EQUICONTINUOUS r9b-a-s 'RR-MS r9b-a-sub)
  (lambda ()
    (fact 'equicont-subseq r9b-a-s 'RR-MS r9b-a-fam r9b-a-del)
    (ass)))

;;; ---- the bridge ---------------------------------------------------------

;; The antecedent is READ OFF the instance, never rebuilt: its binder is the
;; bridge's own and a reconstruction would match nothing.
(define r9b-a-BR (dk-fact! 'ascoli-dense-bridge r9b-a-s r9b-a-sub))

(if (not (and (pair? r9b-a-BR) (eq? (car r9b-a-BR) 'IMPLIES)))
    (error "rake-ascoli: the bridge did not land as an implication"
           (expression->string r9b-a-BR)))

(define r9b-a-ANT (cadr r9b-a-BR))

(have! r9b-a-ANT
  (lambda ()
    (witness! r9b-a-dseq (lambda () (dk-conj-close! (lambda () (ass)))))))

(define r9b-a-EXG (dk-landed-1 (lambda () (detach! r9b-a-BR))))
(define r9b-a-gv (dk-skolem! r9b-a-EXG))

(witness! r9b-a-del
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
           (ass)
           (witness! r9b-a-gv
             (lambda () (dk-conj-close! (lambda () (ass))))))))))

(r9b-qed! 'ascoli-sequential-from-diagonal)
(topic! 'ascoli-sequential-from-diagonal 'topology)
(gloss! 'ascoli-sequential-from-diagonal
  "Ascoli-Arzela, sequential form, reduced to its one missing rung.  Given the
   hypotheses of ascoli-arzela-sequential, an inhabited carrier (the guard
   compact-metric-is-separable carries: the empty metric space has no dense
   SEQUENCE), and a POINTWISE DIAGONAL -- for every dense sequence dseq some
   strictly monotone del makes SUBSEQ(fam, del) convergent at every dseq(m) --
   the conclusion of Ascoli-Arzela follows: compact-metric-is-separable supplies
   dseq, equicont-subseq and subseq-apply carry the hypotheses to the
   subsequence, and ascoli-dense-bridge finishes.  What remains unproven in the
   library is exactly the diagonal antecedent.")

;;; =====================================================================
;;; WHAT IS LEFT, and the exact statements.  See the report for the
;;; measurements; the short form:
;;;
;;;   (1) THE ANALYTIC BRICK, absent from the tree in every form (there is no
;;;       Bolzano-Weierstrass, no monotone-subsequence lemma, no limsup, and no
;;;       concrete SEQ-COMPACT or TOTALLY-BOUNDED space):
;;;
;;;         forall h, bd, J.  h in FUN(NN, RR)  =>  (forall i in NN. abs(h i) <= bd)
;;;           =>  J in INF-SUBSETS(NN)
;;;           =>  forsome b_.  b_ in INF-SUBSETS(NN)  and  SUBSET(b_, J)
;;;                 and forsome p in RR. CONVERGES-ALONG(RR-MS, h, b_, p)
;;;
;;;       This is block-step-converges (rake-block-tower.scm:162) with
;;;       "bounded real sequence" in place of "sequence in a SEQ-COMPACT space",
;;;       and it is the ONLY place the missing metric SUBSPACE structure is
;;;       really wanted: with a subspace [-bd, bd] and its sequential
;;;       compactness the existing block-step-converges would be cited directly.
;;;
;;;   (2) THE TOWER, a re-run of rake-block-tower.scm part B with (1) as the
;;;       totality of the dependent choice and RR-MS as every factor, then
;;;       diagonalization + coord-block-estimate as in rake-diagonal-subseq.scm
;;;       L1, yielding the diagonal antecedent of the theorem above.
;;; =====================================================================
