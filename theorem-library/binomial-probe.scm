;;; binomial-probe.scm -- validation harness for the binomial build, NOT loaded.
;;; Assumes finsum-additive.scm + binomial.scm are loaded (they are, in load.scm).
;;; Run:
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;       --load theorem-library/binomial-probe.scm

(display "\n===== A. capstone + machinery all installed? =====\n")
(for-each
  (lambda (nm)
    (display ";;   ") (display nm) (display " : ")
    (display (if (hash-table-ref/default *theorem-table* nm #f) "PRESENT" "ABSENT"))
    (newline))
  '(binomial-theorem
    ord-segment-insert ring-power-succ
    finsum-add finsum-ring-distrib-left finsum-ring-scalar-zz finsum-reindex
    ;; the pre-existing pieces the proof also leans on:
    ring-power-zero ring-power-add ring-left-dist ring-right-dist
    zz-act-one zz-act-add finsum-insert finsum-singleton finsum-empty
    ord-segment-nn-succ ord-segment-self
    choose-n-0 choose-succ nn-minus-0 nn-minus-succ))

(display "\n===== B. (ni) sets up base + step from the INSTALLED statement =====\n")
(sp (make-wff (lookup-theorem 'binomial-theorem)))
(di)                                   ; intro the outer eigenvar R
(di)                                   ; assume IS-COMMUTATIVE-RING R; goal FORALL n ...
(quietly (lambda () (ni)))             ; induct on n
(let ((leaves (filter (lambda (s) (and (not (sequent-node-grounded? s))
                                       (null? (sequent-node-in-arrows s))))
                      (dg-ungrounded-nodes (proof-state-dg *ps*)))))
  (for-each
    (lambda (g)
      (display ";;   LEAF: ")
      (display (expression->string (wff-formula (sequent-node-assertion g))))
      (newline))
    leaves))

(display "\n===== C. smoke-test: does ring-power-succ fire as a goal rewrite? =====\n")
;; A tiny standalone goal that the support should rewrite.
(sp (make-wff
     '(IMPLIES (IS-COMMUTATIVE-RING R) (IMPLIES (IN x (A R)) (IMPLIES (IN m NN)
               (= (RING-POWER R x (succ m)) ((MUL R) (RING-POWER R x m) x)))))))
(di) (di) (di)
(display ";; goal before: ")
(display (expression->string (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(newline)
(bc* 'ring-power-succ)
(display ";; after (bc* 'ring-power-succ): open goals = ")
(display (length (proof-open-goals *ps*)))
(display "  (the support backchained; remaining goals are its typing antecedents)\n")
(display ";; proof-done? ")
(display (proof-done? *ps*))
(newline)
