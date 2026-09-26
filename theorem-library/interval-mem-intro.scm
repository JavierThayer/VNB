;;; interval-mem-intro.scm -- membership INTRODUCTION for INTERVAL, proven.
;;;
;;;     forall a, b, i.  i in NN  =>  a <= i  =>  i <= b  =>  i in INTERVAL(a, b)
;;;
;;; The support of the same name in structure-library/order-lemmas.scm:327 is
;;; the converse of interval-lo / interval-hi (theorem-library/interval-basics),
;;; and it is SEP-membership introduction and nothing else: INTERVAL(a,b) is
;;; the def-functoid  { i in NN : a <= i and i <= b }  (structure-library/matrix),
;;; `mac' unfolds it in the GOAL, and `sep-mi' asks for exactly the two
;;; hypotheses `di' just landed -- the NN typing and the conjunction of the two
;;; bounds.
;;;
;;; PLAN.  (dk-peel-to! 'IN) (mac 'INTERVAL) (sep-mi), then every leaf is closed
;;; from the context (the AND leaf is split first).  Measured: a single `di'
;;; lands only (IN i NN) here -- the guarded FORALL i -- and leaves the two
;;; bound IMPLIES on the goal, so the peel loops on the head.
;;;
;;; WINDOW.  Cites nothing but the INTERVAL macete (structure-library/matrix)
;;; and the kernel SEP rules, so lo = the first slot after driver-kit / proof-debt
;;; (any theorem-library slot works).  hi = theorem-library/interval-widen, the
;;; earliest `fact' of interval-mem-intro.  Natural home: beside interval-lo /
;;; interval-hi in theorem-library/interval-basics.
;;;
;;; Helper prefix: imi-.

;; Close every open leaf from the context, splitting conjunctions.  ERRORS if
;; a pass closes nothing -- a leaf that `ass' cannot take must not spin.
(define (imi-close-all!)
  (let loop ()
    (let ((ls (proof-leaves)))
      (if (not (null? ls))
          (begin
            (dk-focus! (car ls))
            (from-context!)
            (if (>= (length (proof-leaves)) (length ls))
                (error "imi-close-all!: leaf not closed from context" (dk-goal)))
            (loop))))))

(sp (make-wff '(FORALL a (FORALL b (FORALL i (IMPLIES (IN i NN)
     (IMPLIES (<= a i) (IMPLIES (<= i b) (IN i (INTERVAL a b))))))))))
(dk-peel-to! 'IN)         ; lands (IN i NN), (<= a i), (<= i b) -- one `di'
                          ; takes the guarded FORALL and stops; loop on the head
(mac 'INTERVAL)           ; goal: (IN i (SEP i NN (AND (<= a i) (<= i b))))
(sep-mi)                  ; leaves: (IN i NN)  and  (AND (<= a i) (<= i b))
(imi-close-all!)
(qed 'interval-mem-intro)
(topic! 'interval-mem-intro 'plumbing)
