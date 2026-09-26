;;; theorem-library/rake-fin-enum.scm -- fin-enum-is-bijection, moved out of
;;; theorem-library/rake-inverse-bij.scm on 2026-09-20 (batch 9-B, CARD := CARD-STAR).
;;;
;;;   fin-enum-is-bijection   S in SET, CARD S in NN
;;;                             =>  FIN-ENUM(S) in BIJECTION(ORD-SEGMENT(CARD S), S)
;;;
;;; WHY IT MOVED.  It is the ONE theorem of rake-inverse-bij.scm that rests on a CARD
;;; law (card-finite-bij); the rest of that file -- inverse-bij-{right,left,in-fun,
;;; is-bijection} and ord-segment-self -- is CARD-free and is needed by the CARD
;;; development, which now loads far above.  So the file was split at this theorem and
;;; this half loads immediately after theorem-library/card-laws.scm.  Its earliest citer
;;; is theorem-library/finsum-type-proof, well below.
;;;
;;; The `rkn-' helper block is copied verbatim from rake-inverse-bij.scm; each
;;; theorem-library file gets its own environment, so the two copies do not meet.
;;; The original is archive/2026-09-20-card-defined/rake-inverse-bij-before-split.scm.

(define (rkn-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkn: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkn: proof not complete" name))))

(define (rkn-head? f h) (and (pair? f) (eq? (car f) h)))

;; close every leaf a branching tactic opened, by `ass'
(define (rkn-close-opened! thunk)
  (for-each (lambda (l)
              (dk-focus! l)
              (let ((g (dk-goal)))
                (if (and (rkn-head? g '=) (equal? (cadr g) (caddr g))) (rfl) (ass))))
            (dk-opened thunk)))

;; unfold (IN PH (BIJECTION D C)) in the context and split; return the three
;; conjuncts as (fun injective surjective).
(define (rkn-open-bijection! f)
  (let ((atoms (dk-split-all! (dk-landed* (lambda () (mac-h 'bijection-membership-iff f))))))
    (list (dk-pick (lambda (a) (rkn-head? a 'IN)) "the FUN typing")
          (dk-pick (lambda (a) (and (rkn-head? a 'FORALL)
                                    (rkn-head? (caddr a) 'IMPLIES)
                                    (rkn-head? (caddr (caddr a)) 'FORALL)))
                   "injectivity")
          (dk-pick (lambda (a) (and (rkn-head? a 'FORALL)
                                    (rkn-head? (caddr a) 'IMPLIES)
                                    (rkn-head? (caddr (caddr a)) 'FORSOME)))
                   "surjectivity"))))

;;; ===========================================================================

;;; fin-enum-is-bijection:  S finite => FIN-ENUM(S) in BIJECTION(OS(CARD S), S).
;;; FIN-ENUM S is CHOICE of that class; card-finite-bij says it is inhabited.
;;; (Also proven in theorem-library/finsum-insert.scm, which loads LATER once
;;; this file is in place -- that block is the one to delete.)
(sp (make-wff '(FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S)))))))
(dk-peel!)
(let* ((sv  (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (eq? (caddr f) 'SET))) "S in SET")))
       (cls (list 'BIJECTION (list 'ORD-SEGMENT (list 'CARD sv)) sv)))
  (mac 'FIN-ENUM)
  (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'CARD sv) 'NN))
         (lambda () (dk-conj-close! (lambda () (ass)))))
  (dk-fact! 'card-finite-bij sv)
  (dk-fact! 'choice-axiom cls)
  (ass))
(rkn-check! 'fin-enum-is-bijection)
(qed 'fin-enum-is-bijection)

