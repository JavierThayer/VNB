;;; scratch-succmono.scm -- ord-segment-succ-monotone:
;;;   n in NN  =>  forall i in ORD-SEGMENT(n).  succ i in ORD-SEGMENT(succ n).
;;; NN induction on n.  Base: os(0) empty.  Step: split i in os(succ n) via
;;; ord-segment-nn-succ; one mac rewrites BOTH the i-membership antecedent
;;; and the succ-i-membership goal into OR-form.
(load "load.scm")

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL i (IMPLIES (IN i (ORD-SEGMENT n))
          (IN (succ i) (ORD-SEGMENT (succ n)))))))))
(ni)
(display "--- after (ni) ---\n") (show)

;;; base n = 0:  i in ORD-SEGMENT(0) is impossible
(let ((i0 (eigen-name 'i *fresh-counter*)))
  (di)
  (ta 'ord-segment-zero-no-members)
  (inst '(FORALL k (NOT (IN k (ORD-SEGMENT 0)))) i0)
  (ai `(NOT (IN ,i0 (ORD-SEGMENT 0)))))
(display "--- base done ---\n") (show)

;;; step n -> succ n
(let ((nv (eigen-name 'n *fresh-counter*)))
  (di)                           ; intro n, assume n in NN
  (di)                           ; assume IH
  (cut `(IN (succ ,nv) NN))
  (let ((use-snn (last-node)))
    (ta 'nn-succ-closed)
    (inst '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))) nv)
    (bc `(IMPLIES (IN ,nv NN) (IN (succ ,nv) NN)))
    (ass)
    (refocus! use-snn))
  (let ((iv (eigen-name 'i *fresh-counter*)))
    (di)                         ; intro i, assume i in ORD-SEGMENT(succ n)
    (cut `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,nv)))
                   (IN (succ ,iv) (ORD-SEGMENT (succ (succ ,nv))))))
    (let ((use-imp (last-node)))
      ;; one mac rewrites antecedent i in os(succ n) AND goal succ i in
      ;; os(succ(succ n)) into OR-form.
      (mac 'ord-segment-nn-succ)
      (di)                       ; assume (OR i in os(n), i = n)
      (ai `(OR (IN ,iv (ORD-SEGMENT ,nv)) (= ,iv ,nv)))
      (let ((case2 (last-node)))
        ;; case 1: i in ORD-SEGMENT(n) -- use the IH
        (oi-l)                   ; goal -> (IN (succ i) (ORD-SEGMENT (succ n)))
        (inst `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv))
                                  (IN (succ i) (ORD-SEGMENT (succ ,nv))))) iv)
        (bc `(IMPLIES (IN ,iv (ORD-SEGMENT ,nv))
                      (IN (succ ,iv) (ORD-SEGMENT (succ ,nv)))))
        (ass)
        ;; case 2: i = n
        (refocus! case2)
        (subst `(= ,iv ,nv))     ; goal OR-form, rewrite i -> n
        (oi-r)
        (rfl))
      (refocus! use-imp)
      (bc `(IMPLIES (IN ,iv (ORD-SEGMENT (succ ,nv)))
                    (IN (succ ,iv) (ORD-SEGMENT (succ (succ ,nv))))))
      (ass))))
(display "--- DONE ---\n") (show)
