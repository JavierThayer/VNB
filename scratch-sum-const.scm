;;; scratch-sum-const.scm -- warm-up to the Gauss sum.
;;; Goal: forall n in NN, SUM(ZZ-RING, lambda k. 1, n) = n.

(load "load.scm")

(define const1 '(VNB-LAMBDA k 1))

(define warm-goal
  `(FORALL n (IMPLIES (IN n NN)
     (= (SUM ZZ-RING ,const1 n) n))))

(sp (make-wff warm-goal))
(ni)

;;; ===== BASE: (= (SUM ZZ-RING const1 0) 0) =====
(display "--- base ---\n") (show)
(mac 'sum-zero)
(display "after sum-zero\n") (show)
(mac 'ZERO)
(display "after mac 'ZERO\n") (show)
(mac 'zz-ring-def)
(display "after zz-ring-def\n") (show)
(nth-r)
(display "after nth-r\n") (show)
(rfl)
(display "--- base closed; step in focus ---\n") (show)

;;; ===== STEP =====
(let ((n (eigen-name 'n *fresh-counter*)))
  (di)                  ; peel FORALL n -> n_k, asm (IN n_k NN)
  (di)                  ; peel IMPLIES IH -> asm (= (SUM ZZ-RING const1 n_k) n_k)
  (display "--- step opened ---\n") (show)
  (mac 'sum-succ)
  (display "after sum-succ\n") (show)
  (lam-b)
  (display "after lam-b\n") (show)
  (mac 'ADD)
  (display "after mac 'ADD\n") (show)
  (mac 'zz-ring-def)
  (display "after zz-ring-def\n") (show)
  (nth-r)
  (display "after nth-r\n") (show)
  (subst `(= (SUM ZZ-RING ,const1 ,n) ,n))
  (display "after subst IH\n") (show)
  (mac 'binplus-apply)
  (display "after binplus-apply\n") (show)
  (arith)
  (display "--- step closed ---\n") (show))
