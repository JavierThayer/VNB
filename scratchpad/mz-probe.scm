;;; mz-probe.scm -- exercise minimize! on the smallest instance: vars=(x),
;;; guard=(IN x s), measure = x.  Re-derives the well-ordering of NN from
;;; itself, so it is mathematically vacuous -- but it moves every joint of the
;;; tactic (cut, the two obligations, the SEP set, sep-me, the re-currying).
;;;
;;; The conjuncts of the goal are in the OPPOSITE order to the one minimize!
;;; produces.  That is deliberate: a goal alpha-equivalent to minimize!'s own
;;; MIN lemma makes dg-post! hash-cons the cut into a self-loop (see mz--cut!).
;;;
;;; The heavier tests are the library proofs themselves -- min-degree-entry
;;; (k=2) and class-min-pivot (k=3) -- which load.scm has already run by the
;;; time this file is read.

(sp (make-wff
     '(FORALL s (IMPLIES (AND (SUBSET s NN) (FORSOME n (IN n s)))
        (FORSOME m (AND (FORALL k (IMPLIES (IN k s) (<= m k))) (IN m s)))))))
(di)                                   ; peel FORALL s
(di)                                   ; assume the antecedent
(ai '(AND (SUBSET s NN) (FORSOME n (IN n s))))

(define mzp (minimize! '(x) '(IN x s) 'x))
(display ";;; minimize! witnesses: ") (write (car mzp)) (newline)

(define mzp-w    (car (car mzp)))
(define mzp-type (cadr mzp))
(define mzp-ne   (caddr mzp))

;; --- obligation 1: the measure is an NN.  x in s => x in NN IS (SUBSET s NN).
(set-proof-state-focus! *ps* mzp-type)
(mac-h 'subset-def '(SUBSET s NN))
(ass)

;; --- obligation 2: s is nonempty.  An alpha-variant of the hypothesis, so
;; minimize! found it in context and never cut it: mzp-ne is #f.
(display ";;; nonempty obligation node: ") (write mzp-ne) (newline)
(if mzp-ne (begin (set-proof-state-focus! *ps* mzp-ne) (ass)))

;; --- main goal: the witness minimize! handed back IS a least element.
(set-proof-state-focus! *ps* (car (filter (lambda (n)
                                            (and (not (sequent-node-grounded? n))
                                                 (null? (sequent-node-in-arrows n))))
                                          (dg-ungrounded-nodes (proof-state-dg *ps*)))))
(ew mzp-w)
(di)
(ass)                                  ; minimality  (minimize! landed it verbatim)
(ass)                                  ; membership

(display ";;; mz-probe proof-done? ") (write (proof-done? *ps*)) (newline)
(display ";;; min-degree-entry proven? ")
(write (and (memq 'min-degree-entry *proven-theorem-names*) #t)) (newline)
(display ";;; class-min-pivot proven? ")
(write (and (memq 'class-min-pivot *proven-theorem-names*) #t)) (newline)
(display ";;; mat-equiv-target-is-mat proven? ")
(write (and (memq 'mat-equiv-target-is-mat *proven-theorem-names*) #t)) (newline)
