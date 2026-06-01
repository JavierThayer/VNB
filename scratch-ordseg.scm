;;; scratch-ordseg.scm -- developing the NN-flavored ord-segment-succ lemma.
(load "load.scm")

;;; --- Step A: reverse bridge  succ(n) = succ_ORD(n)  for n in NN -----------
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (succ n) (succ_ORD n))))))
(di)
(mac 'ord-succ-nn)
(rfl)
(qed 'succ-nn-ord)
(display "--- succ-nn-ord installed ---\n")

;;; --- Step B: NN-flavored ord-segment-succ ---------------------------------
;;; Stated prenex (FORALL n (FORALL k (IMPLIES ...))) so the installed
;;; macete is a clean conditional rewrite of  IN k ORD-SEGMENT(succ n).
(sp (make-wff
     '(FORALL n (FORALL k (IMPLIES (IN n NN)
          (IFF (IN k (ORD-SEGMENT (succ n)))
               (OR (IN k (ORD-SEGMENT n)) (= k n))))))))
(di)   ; peels FORALL n, FORALL k
(di)   ; moves  n in nn  into the assumptions
(mac 'succ-nn-ord)
(ta 'ord-segment-succ)
(inst '(FORALL alpha (IMPLIES (IN alpha ORD)
          (FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD alpha)))
                         (OR (IN x (ORD-SEGMENT alpha)) (= x alpha))))))
      'n_1)
(display "--- B: after (inst ... n_1) ---\n") (show)
(cut '(FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD n_1)))
                     (OR (IN x (ORD-SEGMENT n_1)) (= x n_1)))))
(display "--- B: after (cut FORALL-x) ---\n") (show)

;;; Branch [5]: prove  FORALL x (IFF...)  by backchaining ord-segment-succ.
(bc '(IMPLIES (IN n_1 ORD)
        (FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD n_1)))
                       (OR (IN x (ORD-SEGMENT n_1)) (= x n_1))))))
(display "--- B5: after (bc ord-segment-succ@n_1) ---\n") (show)
(ta 'nn-subset-ord)
(inst '(FORALL n (IMPLIES (IN n NN) (IN n ORD))) 'n_1)
(bc '(IMPLIES (IN n_1 NN) (IN n_1 ORD)))
(ass)
(display "--- B5: after closing  n_1 in ord ---\n") (show)

;;; Branch [6]: discharge the cut lemma against the k_2 instance.
(inst '(FORALL x (IFF (IN x (ORD-SEGMENT (succ_ORD n_1)))
                      (OR (IN x (ORD-SEGMENT n_1)) (= x n_1))))
      'k_2)
(ass)
(display "--- B: ord-segment-nn-succ final ---\n") (show)
(qed 'ord-segment-nn-succ)
(display "--- ord-segment-nn-succ installed ---\n")
