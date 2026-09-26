;;; interval-card-in-nn.scm -- an interval with a natural upper bound is finite.
;;;
;;;     interval-card-in-nn:
;;;       forall a, b.  b in NN  =>  CARD(INTERVAL(a, b)) in NN
;;;
;;; Statement UNCHANGED from the support it retires
;;; (structure-library/matrix.scm:106, warranted `well-known'; guarded on the
;;; upper bound alone since 2026-08-12).
;;;
;;; THE PROOF.  INTERVAL(a, b) = { i in NN : a <= i and i <= b } is a subset of
;;; ORD-SEGMENT(succ b):  a member z is in NN (interval-elt-in-nn) and is <= b
;;; (interval-hi); seg-mem-lt reads z in ORD-SEGMENT(succ b) as z < succ b, i.e.
;;; z <= succ b (nn-le-succ + nn-le-trans-guarded) and z /= succ b
;;; (nn-le-imp-neq-succ).  That is the backward half of seg-mem-succ-le, inlined
;;; because seg-mem-succ-le itself bills co-le-trans (the unguarded transitivity,
;;; a C leaf awaiting a user decision) and the half needed here does not need it.
;;; ORD-SEGMENT(succ b) is a set (nn-succ-closed, nn-subset-ord,
;;; ord-segment-is-set) whose cardinal is succ b (card-segment), hence in NN.
;;; INTERVAL(a, b) is a set (interval-in-set).  card-subset-nn -- a subset of a
;;; finite set is finite -- closes the goal.  No induction here: the induction
;;; is inside card-subset-nn.
;;;
;;; LOAD WINDOW [card-subset-nn + 1, triple-entry-proof).  lo is forced by
;;; card-subset-nn (theorem-library/card-subset-nn.scm, load.scm:983); every
;;; other citation is far above it (interval-basics at load.scm:594,
;;; nn-order-ord and nn-order-basics for the NN order bricks, ord-segment-arith
;;; for seg-mem-lt, and the primitive shelf: number-systems, ordinals,
;;; cardinality).  hi is forced by the earliest citer of the support,
;;; theorem-library/triple-entry-proof.scm (load.scm:1461).  The slot right after
;;; card-subset-nn is inside the window.
;;;
;;; Helper prefix: icn-.

;;; --- file-local helpers (icn- prefix) -----------------------------------

;; ORD-SEGMENT(succ b) is a set whose cardinal is in NN, for b in NN in context.
(define (icn-segment-finite! b)
  (let ((seg (list 'ORD-SEGMENT (list 'succ b))))
    (fact 'nn-succ-closed b)                       ; (IN (succ b) NN)
    (fact 'nn-subset-ord (list 'succ b))           ; (IN (succ b) ORD)
    (fact 'ord-segment-is-set (list 'succ b))      ; (IN seg SET)
    (fact 'card-segment (list 'succ b))            ; (= (CARD seg) (succ b))
    (have! (list 'IN (list 'CARD seg) 'NN)
      (lambda ()
        (subst (list '= (list 'CARD seg) (list 'succ b)))   ; goal -> (IN (succ b) NN)
        (ass)))
    (have! (list 'AND (list 'IN seg 'SET) (list 'IN (list 'CARD seg) 'NN)))))

;; INTERVAL(a, b) is a set and a subset of ORD-SEGMENT(succ b), as the
;; conjunction card-subset-nn's inner antecedent wants.
(define (icn-interval-subset! a b)
  (let* ((ivl  (list 'INTERVAL a b))
         (seg  (list 'ORD-SEGMENT (list 'succ b)))
         (incl (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z ivl) (list 'IN 'z seg)))))
    (fact 'interval-in-set a b)                    ; (IN ivl SET)
    (have! incl
      (lambda ()
        (dk-landed-1 (lambda () (di)))             ; lands (IN z ivl)
        (let ((z (cadr (dk-goal))))                ; read the eigenvariable off the GOAL
          (fact 'interval-elt-in-nn a b z)         ; (IN z NN)
          (fact 'interval-hi a b z)                ; (<= z b)
          ;; z in ORD-SEGMENT(succ b)  <-  z < succ b  <-  z <= succ b and z /= succ b.
          ;; This is the backward half of seg-mem-succ-le, inlined: that theorem
          ;; bills co-le-trans (unguarded, a C leaf), and every brick of the half
          ;; needed here is proven modulo 0.
          (mac 'seg-mem-lt)                        ; goal -> (< z (succ b)); guards in context
          (mac '<)                                 ; goal -> (AND (<= z (succ b)) (NOT (= z (succ b))))
          (fact 'nn-le-succ b)                     ; (<= b (succ b))
          (fact 'nn-le-trans-guarded z b (list 'succ b))   ; (<= z (succ b))
          (fact 'nn-le-imp-neq-succ b z)           ; (NOT (= z (succ b)))
          (from-context!))))
    (have! (list 'AND (list 'IN ivl 'SET) incl))))

;;; -----------------------------------------------------------------------
;;; THE THEOREM.

(quietly (lambda ()
  (sp (make-wff '(FORALL a (FORALL b (IMPLIES (IN b NN)
        (IN (CARD (INTERVAL a b)) NN))))))
  (di)                                             ; lands (IN b NN)
  (let* ((g   (dk-goal))                           ; (in (card (interval a b)) nn)
         (ivl (cadr (cadr g)))
         (a   (cadr ivl))
         (b   (caddr ivl))
         (seg (list 'ORD-SEGMENT (list 'succ b))))
    (icn-segment-finite! b)
    (icn-interval-subset! a b)
    (fact 'card-subset-nn seg ivl)
    (ass))))
(qed 'interval-card-in-nn)
(topic! 'interval-card-in-nn 'combinatorial)
