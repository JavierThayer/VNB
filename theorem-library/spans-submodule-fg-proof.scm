;;; spans-submodule-fg-proof.scm -- THE DESCENT (under construction).
;;; Temporarily re-asserts spans-submodule-fg so the library loads while L1/L2
;;; and the descent skeleton are built; the induction proof replaces this.
(support 'spans-submodule-fg
  '(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
     (FORALL n (IMPLIES (IN n NN)
      (FORALL u (IMPLIES (IN u (MAT n 1 (VEC md)))
       (FORALL bm (IMPLIES (IS-SUBMODULE md bm)
        (IMPLIES (SPANS md n u bm)
         (FORALL sm (IMPLIES (IS-SUBMODULE md sm)
          (IMPLIES (SUBSET sm bm)
           (FORSOME k (AND (AND (IN k NN) (<= k n))
            (FORSOME w (AND (IN w (MAT k 1 (VEC md)))
                            (SPANS md k w sm))))))))))))))))))
(warrant! 'spans-submodule-fg 'informal "TEMP re-assert; descent proof pending.")
