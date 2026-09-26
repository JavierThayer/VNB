;;; theorem-library/ascoli-assembly.scm -- equicont-dense-conv-implies-unif-cauchy.
;;;
;;; MOVED here 2026-09-15 from the tail of ascoli-analytic-cores.scm.  It composes
;;; equicont-dense-conv-ptwise-cauchy (proven there) with
;;; ptwise-cauchy-compact-equicont-unif -- until tonight an asserted `reference'
;;; support, now PROVEN in theorem-library/ptwise-cauchy-unif.scm, which has to load
;;; after ascoli-analytic-cores (it unfolds IS-PTWISE-CAUCHY / IS-UNIF-CAUCHY, defined
;;; there) and therefore after the place this block used to sit.  Load order:
;;; ascoli-analytic-cores -> ball-is-open -> ptwise-cauchy-unif -> THIS -> ascoli-bridge.
;;;
;;; `acc-peel!' is copied from ascoli-analytic-cores.scm (per-file environments).

(define (acc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1)))
          n))))

;;; equicont-dense-conv-implies-unif-cauchy: what ascoli-bridge.scm asserted.
;;; Two citations; the analytic half is proved, the finite-subcover half is
;;; ptwise-cauchy-compact-equicont-unif, proven (2026-09-15).
(sp (make-wff
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IS-EQUICONTINUOUS s RR-MS fam)
      (forsome-guarded 'dseq '(IS-DENSE-SEQ s dseq) '(CONVERGES-ON s fam dseq)))
    '(IS-UNIF-CAUCHY s fam))))
(acc-peel!)
(fact 'equicont-dense-conv-ptwise-cauchy 's 'fam)
(fact 'ptwise-cauchy-compact-equicont-unif 's 'fam)
(ass)
(qed 'equicont-dense-conv-implies-unif-cauchy)
(topic! 'equicont-dense-conv-implies-unif-cauchy 'analysis)
(gloss! 'equicont-dense-conv-implies-unif-cauchy
  "On a COMPACT metric space, an equicontinuous family that converges at every
   term of a dense sequence is UNIFORMLY Cauchy.  Was an asserted `reference'
   support (the file called it `the 3-epsilon core'); it is now the composition
   of a proved pointwise-Cauchy lemma with the proved compactness rung -- modulo 0
   since 2026-09-15.")


