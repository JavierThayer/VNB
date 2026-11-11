;;; ccr1109a2-metric.scm -- wave of 2026-11-09/10 (agent CCR-1109-A2), wired 2026-11-10 from scratchpad/ccr1109a2/ccr1109a2-metric.scm.
;;; Library: analysis.

;;; ccr1109a2-metric.scm -- A CONVERGENT SEQUENCE IN A METRIC SPACE IS CAUCHY.  CLAUDE.md listed "no general
;;; converges-implies-cauchy" as an open item; the tree had only the TVS-net form (tvs-convergent-net-cauchy).
;;; Used by CCR.pdf Proposition 1.47 (theorem-library/ccr1109a2-nv.scm).  Agent CCR-1109-A2, wave 2026-11-09.
;;; Destination: theorem-library/ccr1109a2-metric.scm.  Library: analysis (metric spaces).
;;; LOAD WINDOW: after structure-library/metric-completeness (IS-CAUCHY-SEQ, CONVERGES-TO), metric-space laws
;;; (metric-triangle, metric-sym, metric-dist-real), pos-rr-bridges / rr-halving (dk-halve!); before
;;; ccr1109a2-nv.  Helper prefix c9m-.

(sp (make-wff '(FORALL s (FORALL f (FORALL cml (IMPLIES (CONVERGES-TO s f cml) (IS-CAUCHY-SEQ s f)))))))
(dk-peel!)
(let* ((_ (dk-iff-fwd! (dk-cite! 'converges-to 's 'f 'cml)))
       (law (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'POS-RR))) "the convergence law"))
       (cs (dk-cite! 'is-cauchy-seq 's 'f)))
  (dk-have! (caddr cs)
    (lambda ()
      (dk-conj-close!
        (lambda ()
          (if (not (dk-ass!))
              (let* ((ls (dk-peel!))
                     (eps (dk-landed-eps ls))
                     (_e (dk-cite! 'rr-pos-rr-in-rr eps))
                     (d (dk-halve! eps))
                     (nb (dk-skolem! (dk-chain-ass! (dk-apply! law d))))
                     (lw (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'cml) (dk-contains? f nb))) "the tail law")))
                (ew nb)
                (dk-conj-close!
                  (lambda ()
                    (if (not (dk-ass!))
                        (let* ((ls2 (dk-peel!))
                               (vs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'NN) (symbol? (cadr f)))) ls2)))
                               (m (car vs)) (n (cadr vs)))
                          (dk-split-all!)
                          (for-each (lambda (v) (dk-cite! 'fun-apply-type-c 'f 'NN '(PTS s) v)) (list m n))
                          (let* ((h1 (dk-chain-ass! (dk-apply! lw m)))
                                 (h2 (dk-chain-ass! (dk-apply! lw n)))
                                 (tr (dk-chain-ass! (dk-cite! 'metric-triangle 's `(f ,m) 'cml `(f ,n))))
                                 (sy (dk-chain-ass! (dk-cite! 'metric-sym 's 'cml `(f ,n)))))
                            (dk-chain-ass! (dk-cite! 'metric-dist-real 's `(f ,m) 'cml))
                            (dk-chain-ass! (dk-cite! 'metric-dist-real 's 'cml `(f ,n)))
                            (dk-chain-ass! (dk-cite! 'metric-dist-real 's `(f ,n) 'cml))
                            (dk-chain-ass! (dk-cite! 'metric-dist-real 's `(f ,m) `(f ,n)))
                            (dk-ineq! h1 h2 tr sy `(= (+ ,d ,d) ,eps)))))))))))))
  (dk-iff-bwd! cs)
  (dk-close-if-asm!))
(qed 'metric-converges-to-cauchy)

(sp (make-wff '(FORALL s (FORALL f (IMPLIES (CONVERGES s f) (IS-CAUCHY-SEQ s f))))))
(dk-peel!)
(let* ((iff (dk-cite! 'converges 's 'f)) (_ (dk-iff-fwd! iff)) (l (dk-skolem! (caddr iff))))
  (dk-chain-ass! (dk-cite! 'metric-converges-to-cauchy 's 'f l))
  (dk-close-if-asm!))
(qed 'metric-convergent-cauchy)
