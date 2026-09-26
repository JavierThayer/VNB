;;; bt-shims.scm -- the five "Bernstein typing" shims of theorem-library/binomial.scm,
;;; PROVEN.
;;;
;;; binomial.scm:76-80 asserts, as `well-known' supports, five one-line facts that
;;; binomial-proof and the bernstein-* drivers cite by the dozen (60-65 bills each):
;;;
;;;     bt-nn-in-zz      forall n in NN.  n in ZZ
;;;     bt-succ-in-nn    forall n in NN.  succ n in NN
;;;     bt-neg1-in-zz    0 - 1 in ZZ
;;;     bt-neg1-neg      0 - 1 < 0
;;;     bt-lt-succ       forall n in NN.  n < succ n
;;;
;;; None of them is mathematics the library lacks.  The first two are VERBATIM the
;;; primitive axioms `nn-subset-zz' and `nn-succ-closed' of number-systems.scm --
;;; the same species as eq-sym in equality-basics.scm, an asserted duplicate of a
;;; fact the base theory has for free.  The third is `zz-sub-in-zz'
;;; (binary-minus-laws.scm, proven) at 0 and 1.  The fourth is a ground linear
;;; inequality over literals, which the `ineq' oracle decides with no premise.
;;; The fifth unfolds `<' (order-predicates.scm: `<= and not =') into two proven
;;; NN facts, `nn-le-succ' and `nn-le-imp-neq-succ' (nn-order-ord.scm), the
;;; second instantiated at j := k := n against `nn-le-refl' (nn-order-basics.scm).
;;;
;;; The statements are the supports' statements UNCHANGED, so each `qed' below
;;; re-installs the same statement over the asserted one.
;;;
;;; LOAD WINDOW.  Every citation must precede this file, and this file must
;;; precede the first citer.  0-based over *vnb-files* (load.scm):
;;;     nn-subset-zz, nn-succ-closed, zz-zero-in, zz-one-in   number-systems       34
;;;     `<'                                                    order-predicates     39
;;;     the supports themselves                                theorem-library/binomial 123
;;;     zz-sub-in-zz                                           binary-minus-laws   161
;;;     nn-le-succ, nn-le-imp-neq-succ                         nn-order-ord        165
;;;     nn-le-refl                                             nn-order-basics     167   <- forces lo
;;;     first citer                                            binomial-proof      318   <- forces hi
;;; so the window is [168, 318): anywhere after nn-order-basics and before
;;; binomial-proof.
;;;
;;; Helper prefix: bts-.

;; Peel the leading FORALL/IMPLIES prefix, guarded on progress (zb-peel! shape).
(define (bts-peel!)
  (let loop ((fuel 12))
    (let ((before (dk-goal)))
      (if (and (> fuel 0) (memq (car before) '(FORALL IMPLIES)))
          (begin (di)
                 (if (equal? (dk-goal) before)
                     (error "bts-peel!: di made no progress on" before)
                     (loop (- fuel 1))))))))

;;; ---- bt-nn-in-zz: verbatim nn-subset-zz --------------------------------
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN n ZZ)))))
(bts-peel!)
(fact 'nn-subset-zz 'n)
(ass)
(qed 'bt-nn-in-zz)
(topic! 'bt-nn-in-zz 'plumbing)

;;; ---- bt-succ-in-nn: verbatim nn-succ-closed ----------------------------
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN)))))
(bts-peel!)
(fact 'nn-succ-closed 'n)
(ass)
(qed 'bt-succ-in-nn)
(topic! 'bt-succ-in-nn 'plumbing)

;;; ---- bt-neg1-in-zz: zz-sub-in-zz at 0, 1 -------------------------------
(sp (make-wff '(IN (- 0 1) ZZ)))
(fact 'zz-zero-in)
(fact 'zz-one-in)
(fact 'zz-sub-in-zz 0 1)
(ass)
(qed 'bt-neg1-in-zz)
(topic! 'bt-neg1-in-zz 'plumbing)

;;; ---- bt-lt-succ: n < succ n, i.e. n <= succ n and n /= succ n ----------
;;; `mac '<' unfolds the goal to the conjunction; nn-le-succ gives the first
;;; conjunct, and nn-le-imp-neq-succ at k := n, j := n (its antecedent n <= n
;;; is nn-le-refl) gives the second.  `di' splits the AND; `ass' closes each.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (< n (succ n))))))
(bts-peel!)
(mac '<)
(fact 'nn-le-succ 'n)
(fact 'nn-le-refl 'n)
(fact 'nn-le-imp-neq-succ 'n 'n)
(di)
(ass)
(ass)
(qed 'bt-lt-succ)
(topic! 'bt-lt-succ 'inequalities)

;;; ---- bt-neg1-neg: 0 - 1 < 0, ground ------------------------------------
;;; Ground arithmetic over literals.  order-predicates.scm says ground decisions
;;; on `<' go through the unfold via the iff, so: `mac '<' opens the
;;; conjunction, `di' splits it, and the ground evaluator closes each half
;;; (0 - 1 <= 0, then not(0 - 1 = 0)).  Bills `[oracles: arith]'.  A bare
;;; `(ineq)' also closes the original goal in one step, billing
;;; `[oracles: ineq]' -- the Farkas certificate ((goal . 1)); either way a
;;; ground literal fact is decided by a trusted evaluator, and there is no
;;; axiom-only route short of rebuilding it from binary-minus-def and the RR
;;; order axioms.
(sp (make-wff '(< (- 0 1) 0)))
(mac '<)
(di)
(arith)
(arith)
(qed 'bt-neg1-neg)
(topic! 'bt-neg1-neg 'inequalities)
